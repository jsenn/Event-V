//! The first refinement of the abstract Snakes and Ladders model introduces 2 new concepts:
//! 1. The board itself
//! 2. Dice rolls
//! 
//! In the abstract machine, the board was completely abstracted away to just its size, and turns
//! could take a place to any arbitrary square. Here, the board is fully represented as described
//! below. Player movements are constrained by rolls of 6-sided dice, and by the board.
//! 
//! # Board Representation
//! A snakes and ladders board is a linear sequence of squares from the starting square to the
//! final winning square. A player moves forward along the board by the number of squares shown on
//! the dice after their roll. If the new square is at the foot of a **ladder**, the player
//! immediately moves their piece to the square at which the top of the ladder resides; if instead
//! they land at the head of a snake, they move backwards to the square to which the snake's tail
//! is pointing.
//! 
//! We model the board as a sequence of integers. Each integer represents the number of squares
//! forward or backward a player must move upon landing on that square. A square that sits at the
//! base of a ladder will have a positive number, one that sits at the head of a snake will have a
//! negative number, and ordinary squares will take the value 0.
//! 
//! # Board invariants
//! There are a few properties a Snakes and Ladders board must have in order to be valid:
//! 1. It must have at least 2 squares (a start and an end), otherwise the game will end before
//!    anyone can take a turn.
//! 2. Snakes and Ladders can't send you off of the board.
//! 3. The first square must not have a snake head or ladder base, otherwise the square it leads to
//!    would effectively be the first square on the board. Similarly, the last square must not have
//!    a snake or ladder, otherwise the game would not be winnable.
//! 4. Snakes and ladders cannot chain together. This one isn't strictly necessary but it does
//!    simplify the model. This guarantees that you only have to do one board lookup to find a
//!    player's destination square after a roll, avoiding recursive lookups.
//! 5. Finally, in order for the game to be winnable, we require that at every square on the board,
//!    there is some square within a dice roll that will make forward progress. Note that this is
//!    much stronger than necessary: there are perfectly winnable boards with squares that send you
//!    temporarily backwards. However, it is tedious to prove for any given board that it is
//!    winnable in the abstract sense, but it is trivial for Z3 to prove automatically that every
//!    square can make forward progress.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

use crate::abs;
use crate::shared::DiceRoll;

machine! {

machine Board refines abs::Abs {
    context {
        board: Seq<int>,
        player_count: nat,
    }

    valid: |context| {
        // Someone is playing
        &&& context.player_count > 0
        // Board isn't degenerate (at least one turn to traverse)
        &&& context.board.len() > 1
        // Snakes and ladders can't take you off the board
        &&& forall |i: int| #![trigger context.board[i]]
                0 <= i < context.board.len() ==>
                    0 <= i + context.board[i] < context.board.len()
        // No snakes or ladders on first or last square
        &&& context.board[0] == 0 && context.board[context.board.len() - 1] == 0
        // Snakes and ladders cannot chain together
        &&& forall |i: int| #![trigger context.board[i]]
                0 <= i < context.board.len() && context.board[i] != 0 ==>
                    context.board[i + context.board[i]] == 0
        // Board is winnable: every square other than the winning square has another square at most
        // 6 squares ahead that will permit forward progress. e.g. having 6 snakes in a row that
        // push you backwards would be illegal.
        &&& forall |i: int| #![trigger context.board[i]]
                0 <= i < context.board.len() - 1 ==> {
                    ||| i+1 + context.board[i+1] > i
                    ||| i+2 + context.board[i+2] > i
                    ||| i+3 + context.board[i+3] > i
                    ||| i+4 + context.board[i+4] > i
                    ||| i+5 + context.board[i+5] > i
                    ||| i+6 + context.board[i+6] > i
                }
    }

    state {
        player_positions: Seq<int>,
        next_player: int,
    }

    lift_context: |context| abs::Context {
        board_size: context.board.len(),
        player_count: context.player_count,
    }

    lift: |state| abs::Abs {
        player_positions: state.player_positions,
        next_player: state.next_player,
    }

    init: |context| Board {
        player_positions: Seq::new(context.player_count, |i| { 0 }),
        next_player: 0,
    }

    invariant: |context, state| {
        // Players can't sit at the top of a snake or the bottom of a ladder
        &&& forall |player: int| #![trigger state.player_positions[player]]
                0 <= player < state.player_positions.len() ==>
                    context.board[state.player_positions[player]] == 0
    }

    refined event Turn(roll: DiceRoll) {
        lift_in: |context, state| state.take_turn(context, roll)

        guard: |context, state| {
            // Game not over
            &&& !state.lift().is_done(context.lift())
        }

        action: |context, state| {
            let next_pos = state.take_turn(context, roll);
            Board {
                player_positions: state.lift().move_player(state.next_player, next_pos),
                next_player: state.lift().advance_player(),
            }
        }
    }
}

}

verus! {

impl Board {
    pub open spec fn take_turn(self, context: Context, roll: DiceRoll) -> int {
        let curr_pos = self.player_positions[self.next_player];
        Self::step(context, curr_pos, roll)
    }

    /// Compute the square a player at the given position would land on after taking the given
    /// roll, taking into account snakes and ladders.
    pub open spec fn step(context: Context, curr_pos: int, roll: DiceRoll) -> int {
        let roll_pos = curr_pos + roll.value();
        if roll_pos >= context.board.len() {
            context.board.len() - 1
        } else {
            roll_pos + context.board[roll_pos]
        }
    }

    /// Determine if it is possible to win the game from the given position within a number of
    /// steps given by `fuel`.
    pub open spec fn can_win_from(context: Context, pos: int, fuel: nat) -> bool
        decreases fuel
    {
        // Base case: `pos` *is* the winning square
        ||| pos == context.board.len() - 1
        // Induction: we can win from some square within a dice roll of `pos`
        ||| (fuel > 0 && exists |roll: DiceRoll|
                Self::can_win_from(context, Self::step(context, pos, roll), (fuel - 1) as nat))
    }
}

}

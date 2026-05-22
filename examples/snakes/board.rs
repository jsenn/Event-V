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
        // 6 squares ahead that will permit forward progress. This rules out any sequence of 6 or
        // more snake heads ahead of some position i where the tail of each snake lands before i.
        // Note that this is a stronger requirement than winnability, but it is much easier for Z3
        // to prove.
        &&& forall |i: int|
                0 <= i < context.board.len() - 1 ==>
                    #[trigger] context.has_forward_progress(i)
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

impl Context {
    /// Determine whether there is some dice roll that makes forward progress from a given square.
    pub open spec fn has_forward_progress(&self, pos: int) -> bool {
        ||| Board::step(*self, pos, 1) > pos
        ||| Board::step(*self, pos, 2) > pos
        ||| Board::step(*self, pos, 3) > pos
        ||| Board::step(*self, pos, 4) > pos
        ||| Board::step(*self, pos, 5) > pos
        ||| Board::step(*self, pos, 6) > pos
    }
}

impl Board {
    /// Calculate where the next player will land after the given roll.
    pub open spec fn take_turn(self, context: Context, roll: DiceRoll) -> int {
        let curr_pos = self.player_positions[self.next_player];
        Self::step(context, curr_pos, roll.value())
    }

    /// Compute the square a player at the given position would land on after rolling a die
    /// showing `n`, taking into account snakes and ladders.
    pub open spec fn step(context: Context, curr_pos: int, n: nat) -> int {
        let roll_pos = curr_pos + n;
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
        ||| (fuel > 0 && exists |n: nat| #![auto]
                1 <= n <= 6
             && Self::can_win_from(
                    context, Self::step(context, pos, n), (fuel - 1) as nat))
    }
}

// From any given square on the board, you can win in at most board size - 1 - i moves.
// This follows from the requirement that every square permit forward progress for some dice roll.
proof fn lemma_can_win_from(context: Context, i: int, fuel: nat)
    requires
        context.valid(),
        0 <= i < context.board.len(),
        fuel + i >= context.board.len() - 1,
    ensures
        Board::can_win_from(context, i, fuel),
    decreases context.board.len() - i,
{
    if i < context.board.len() - 1 {
        assert(context.has_forward_progress(i));
        let n = choose |n: nat| 1 <= n <= 6 && Board::step(context, i, n) > i;
        lemma_can_win_from(context, Board::step(context, i, n), (fuel - 1) as nat);
    }
}

/// The game is winnable from the next player's current position. Since no assumption is
/// made about state beyond validity and the invariant, every reachable state is winnable.
proof fn proof_winnable(context: Context, state: Board)
    requires
        context.valid(),
        Board::invariant(context, state),
    ensures
        Board::can_win_from(
            context, state.player_positions[state.next_player], context.board.len()),
{
    lemma_can_win_from(
        context, state.player_positions[state.next_player], context.board.len());
}

}

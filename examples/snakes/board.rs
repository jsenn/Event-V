//! Here we create an abstract model of a Snakes and Ladders board.
//! 
//! # Board Representation
//! A Snakes and Ladders board is a linear sequence of squares from the starting square to the
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
//! 2. Snakes and ladders can't send you off of the board.
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

use event_v::machine::MachineContext;
use crate::dice::DiceRoll;

verus! {

/// Represents a Snakes and Ladders board. A board is modeled as a sequence of squares. Each square
/// contains an integer which indicates how far forward or backward players must move upon landing.
/// A square that is at the base of a ladder will have a positive number; one that is at the head
/// of a snake will be negative. A value of zero indicates a neutral square.
pub struct Board {
    pub squares: Seq<int>,
}

impl Board {
    /// Get the total number of squares on the board.
    pub open spec fn len(self) -> nat {
        self.squares.len()
    }

    /// Determine if the given square is on the board.
    pub open spec fn in_bounds(self, square: int) -> bool {
        0 <= square < self.len()
    }

    /// Determine if the given square is the final (winning) square.
    pub open spec fn is_winner(self, square: int) -> bool {
        square == self.len() - 1
    }

    /// Compute the resting square of a player currently at the given square after they roll the
    /// given value from the die.
    pub open spec fn roll(self, square: int, roll: DiceRoll) -> int {
        self.follow(square + roll.value())
    }

    /// Compute the resting square of a player who landed on the given square after following any
    /// snakes or ladders on that square.
    pub open spec fn follow(self, roll_square: int) -> int {
        if roll_square >= self.len() {
            self.len() - 1
        } else {
            roll_square + self.squares[roll_square]
        }
    }

    /// Determine whether a player can come to rest at the given square. Returns false if the given
    /// square is at the head of a snake or the bottom of a ladder.
    pub open spec fn is_at_rest(self, square: int) -> bool {
        self.squares[square] == 0
    }

    /// Determine whether there is some dice roll that makes forward progress from a given square.
    pub open spec fn has_forward_progress(self, square: int) -> bool {
        ||| self.roll(square, DiceRoll::One) > square
        ||| self.roll(square, DiceRoll::Two) > square
        ||| self.roll(square, DiceRoll::Three) > square
        ||| self.roll(square, DiceRoll::Four) > square
        ||| self.roll(square, DiceRoll::Five) > square
        ||| self.roll(square, DiceRoll::Six) > square
    }

    /// Determine if the winning square is reachable from the given square.
    pub open spec fn can_win_from(self, square: int) -> bool {
        exists |rolls: nat| self.can_win_from_within(square, rolls)
    }

    /// Determine if the winning square is reachable from the given square within the given
    /// number of dice rolls.
    pub open spec fn can_win_from_within(self, square: int, rolls: nat) -> bool
        decreases rolls
    {
        // Base case: `square` is the winning square
        ||| self.is_winner(square)
        // Induction: some dice roll lands on a square we can win from
        ||| (rolls > 0 && exists |roll: DiceRoll| #![trigger self.roll(square, roll)]
            self.can_win_from_within(self.roll(square, roll), (rolls - 1) as nat))
    }
}

impl MachineContext for Board {
    open spec fn valid(&self) -> bool {
        // Board isn't degenerate (at least one turn to traverse)
        &&& self.len() > 1
        // Snakes and ladders can't take you off the board
        &&& forall |square: int| #![trigger self.follow(square)]
                self.in_bounds(square) ==>
                    self.in_bounds(self.follow(square))
        // No snakes or ladders on first or last square
        &&& self.squares[0] == 0 && self.squares[self.len() - 1] == 0
        // Snakes and ladders cannot chain together
        &&& forall |square: int| #![trigger self.squares[square]]
                self.in_bounds(square) && !self.is_at_rest(square) ==>
                    self.is_at_rest(self.follow(square))
        // Board is winnable: every square other than the winning square has another square at most
        // 6 squares ahead that will permit forward progress. This rules out any sequence of 6 or
        // more snake heads ahead of some square i where the tail of each snake lands before i.
        // Note that this is a stronger requirement than winnability, but it is much easier for Z3
        // to prove.
        &&& forall |square: int| #![trigger self.has_forward_progress(square)]
                self.in_bounds(square) && !self.is_winner(square) ==>
                    self.has_forward_progress(square)
    }
}

/// On a valid board, you can always win within the given number of rolls, as long as there are
/// enough to cover each square between the start and end of the board.
proof fn lemma_valid_implies_winnable_within(board: Board, square: int, rolls: nat)
    requires
        board.valid(),
        board.in_bounds(square),
        rolls + square >= board.len() - 1,
    ensures
        board.can_win_from_within(square, rolls),
    decreases board.len() - square,
{
    if !board.is_winner(square) {
        // Make sure Verus remembers that there is always some dice roll that makes progress
        assert(board.has_forward_progress(square));
        // Choose a specific dice roll with forward progress
        let roll = choose |roll: DiceRoll| board.roll(square, roll) > square;
        // Recurse using that dice roll
        lemma_valid_implies_winnable_within(board, board.roll(square, roll), (rolls - 1) as nat);
    }
}

/// On a valid board, it is possible to win from any square.
pub proof fn lemma_valid_implies_winnable(board: Board, square: int)
    requires
        board.valid(),
        board.in_bounds(square),
    ensures
        board.can_win_from(square),
{
    let max_rolls = (board.len() - square - 1) as nat;
    lemma_valid_implies_winnable_within(board, square, max_rolls);
}

/// Just for demonstration, we construct a realistic snakes and ladders board cribbed from
/// [wikipedia](https://en.wikipedia.org/wiki/Snakes_and_ladders#/media/File:Berrington_Hall_-_snakes_and_ladders_(13826426425).jpg)
/// and show that Z3 can automatically prove that it is valid.
proof fn proof_board_valid() {
    let board = Board {
        squares: seq![
            0, 0, 0, 0, 0, 0, 0, 18, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            61, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 34, -22, 0, -41, 0, -39, 0, 41,
            0, -41, 0, 39, -48, 0, 0, 0, -42, 0,
            0, 34, 0, -28, 0, 21, 0, 0, -60, 0,
            0, 0, -72, 0, 0, 0, 0, 0, 0, 20,
            0, 0, -64, 0, 0, 0, 0, 0, 0, 0,
            0, -41, 0, 0, -71, 0, 0, -70, 0, 0

        ],
    };

    assert(board.valid());
}

}
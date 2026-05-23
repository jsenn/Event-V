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

use event_v::machine::MachineContext;

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

    /// Compute the square a player at the given position would land on after rolling a die
    /// showing `n`, taking into account snakes and ladders.
    pub open spec fn step(self, roll_pos: int) -> int {
        if roll_pos >= self.len() {
            self.len() - 1
        } else {
            roll_pos + self.squares[roll_pos]
        }
    }

    /// Determine whether a player can come to rest at the given board position. Returns false if
    /// the given position is at the head of a snake or the bottom of a ladder.
    pub open spec fn is_at_rest(self, pos: int) -> bool {
        self.squares[pos] == 0
    }

    /// Determine if the winning square is reachable from the given board position.
    pub open spec fn can_win_from(self, pos: int) -> bool {
        exists |rolls: nat| self.can_win_from_within(pos, rolls)
    }

    /// Determine if the winning square is reachable from the given board position within the given
    /// number of dice rolls.
    pub open spec fn can_win_from_within(self, pos: int, rolls: nat) -> bool
        decreases rolls
    {
        // Base case: `pos` is the winning square
        ||| pos == self.len() - 1
        // Induction: some dice roll lands on a square we can win from
        ||| (rolls > 0 && exists |n: nat| #![trigger self.step(pos + n)] {
            &&& 1 <= n <= 6
            &&& self.can_win_from_within(self.step(pos + n), (rolls - 1) as nat)
        })
    }

    /// Determine whether there is some dice roll that makes forward progress from a given square.
    pub open spec fn has_forward_progress(self, pos: int) -> bool {
        ||| self.step(pos + 1) > pos
        ||| self.step(pos + 2) > pos
        ||| self.step(pos + 3) > pos
        ||| self.step(pos + 4) > pos
        ||| self.step(pos + 5) > pos
        ||| self.step(pos + 6) > pos
    }
}

impl MachineContext for Board {
    open spec fn valid(&self) -> bool {
        // Board isn't degenerate (at least one turn to traverse)
        &&& self.len() > 1
        // Snakes and ladders can't take you off the board
        &&& forall |i: int| #![trigger self.squares[i]]
                0 <= i < self.len() ==>
                    0 <= i + self.squares[i] < self.len()
        // No snakes or ladders on first or last square
        &&& self.squares[0] == 0 && self.squares[self.len() - 1] == 0
        // Snakes and ladders cannot chain together
        &&& forall |i: int| #![trigger self.squares[i]]
                0 <= i < self.len() && self.squares[i] != 0 ==>
                    self.squares[i + self.squares[i]] == 0
        // Board is winnable: every square other than the winning square has another square at most
        // 6 squares ahead that will permit forward progress. This rules out any sequence of 6 or
        // more snake heads ahead of some position i where the tail of each snake lands before i.
        // Note that this is a stronger requirement than winnability, but it is much easier for Z3
        // to prove.
        &&& forall |i: int|
                0 <= i < self.len() - 1 ==>
                    #[trigger] self.has_forward_progress(i)

    }
}

/// On a valid board, you can always win within the given number of rolls, as long as there are
/// enough to cover each square between the starting position and the end of the board.
proof fn lemma_valid_implies_winnable_within(board: Board, pos: int, rolls: nat)
    requires
        board.valid(),
        0 <= pos < board.len(),
        rolls + pos >= board.len() - 1,
    ensures
        board.can_win_from_within(pos, rolls),
    decreases board.len() - pos,
{
    if pos < board.len() - 1 {
        // Make sure Verus remembers that there is always some dice roll that makes progress
        assert(board.has_forward_progress(pos));
        // Choose a specific dice roll with forward progress
        let n = choose |n: nat| 1 <= n <= 6 && #[trigger] board.step(pos + n) > pos;
        // Recurse using that dice roll
        lemma_valid_implies_winnable_within(board, board.step(pos + n), (rolls - 1) as nat);
    }
}

/// On a valid board, it is possible to win from any square.
pub proof fn lemma_valid_implies_winnable(board: Board, pos: int)
    requires
        board.valid(),
        0 <= pos < board.len(),
    ensures
        board.can_win_from(pos),
{
    let max_rolls = (board.len() - pos - 1) as nat;
    lemma_valid_implies_winnable_within(board, pos, max_rolls);
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
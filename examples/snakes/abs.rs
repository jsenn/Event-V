//! This module contains the most abstract version of Snakes and Ladders. At this level, the board
//! is abstracted away completely; the model only knows the board's size. What the model *does*
//! track:
//! 1. Players' positions on the board
//! 2. Whose turn it is
//! 3. Whether or not anyone has won the game yet.
//! 
//! The single event is `Turn`, which moves the next player to a given square, and passes play to
//! the next player.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

verus! {

pub struct Context {
    pub board_size: nat,
}

impl Context {
    pub open spec fn in_bounds(self, square: int) -> bool {
        0 <= square < self.board_size
    }

    pub open spec fn is_winner(self, square: int) -> bool {
        square == self.board_size - 1
    }
}

impl MachineContext for Context {
    open spec fn valid(&self) -> bool {
        // A board with only 1 square would be unplayable as everyone would win immediately!
        self.board_size > 1
    }
}

}

machine! {

machine Abs {
    context: Context

    state {
        // By convention, the next player is always the first in the pair. Each time play passes to
        // the next player we swap them.
        players: (int, int),
    }

    init: |context| Abs {
        players: (0, 0),
    }

    invariant: |context, state| {
        // All players on the board
        &&& context.in_bounds(state.players.0)
        &&& context.in_bounds(state.players.1)
        // At most one winner
        &&& !(context.is_winner(state.players.0) && context.is_winner(state.players.1))
    }

    event Turn(new_square: int) {
        guard: |context, state| {
            // Game not over
            &&& !state.is_done(context)
            // Valid next square
            &&& context.in_bounds(new_square)
        }

        action: |context, state| Abs {
            players: (state.players.1, new_square),
        }
    }
}

}

verus! {

impl Abs {
    pub open spec fn is_done(&self, context: Context) -> bool {
        context.is_winner(self.players.0) || context.is_winner(self.players.1)
    }
}

}

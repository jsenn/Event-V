//! This module contains the most abstract version of Snakes and Ladders. At this level, the board
//! is abstracted away completely; the model only knows the board's size. What the model *does*
//! track:
//! 1. Players' positions on the board
//! 2. Whose turn it is
//! 3. Whether or not anyone has won the game yet.
//! 
//! The single event is `Turn`, which moves the next player to a given board position, and passes
//! play to the next player.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Abs {
    context {
        board_size: nat,
    }

    valid: |context| context.board_size > 1

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
        &&& context.valid_position(state.players.0)
        &&& context.valid_position(state.players.1)
        // At most one winner
        &&& !(context.is_winner(state.players.0) && context.is_winner(state.players.1))
    }

    event Turn(move_to: int) {
        guard: |context, state| {
            // Game not over
            &&& !state.is_done(context)
            // Valid next position
            &&& context.valid_position(move_to)
        }

        action: |context, state| Abs {
            players: (state.players.1, move_to),
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

impl Context {
    pub open spec fn valid_position(&self, pos: int) -> bool {
        0 <= pos < self.board_size
    }

    pub open spec fn is_winner(&self, pos: int) -> bool {
        pos == self.board_size - 1
    }
}

}

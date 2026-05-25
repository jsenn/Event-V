//! Here we refine the abstract snakes and ladders machine to introduce dice rolls and to
//! incorporate the full [board representation][`Board`].

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

use crate::abs;
use crate::dice::DiceRoll;
use crate::board::Board;

machine! {

machine Snakes refines abs::BoardGame {
    context: Board

    state {
        players: (int, int),
    }

    lift_context: |context| abs::Context {
        board_size: context.len(),
    }

    lift: |state| abs::BoardGame {
        players: state.players,
    }

    init: |_| Snakes {
        players: (0, 0),
    }

    invariant: |board, state| {
        // Players can't stay at the top of a snake or the bottom of a ladder
        &&& board.is_at_rest(state.players.0)
        &&& board.is_at_rest(state.players.1)
    }

    refined event Turn(roll: DiceRoll) {
        lift_in: |board, state| {
            board.roll(state.players.0, roll)
        }

        guard: |board, state| {
            // Game not over
            !state.lift().is_done(Snakes::lift_context(board))
        }

        action: |board, state| {
            let next_square = board.roll(state.players.0, roll);
            Snakes {
                players: (state.players.1, next_square),
            }
        }
    }
}

}

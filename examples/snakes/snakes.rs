//! Here we refine the abstract snakes and ladders machine to introduce dice rolls and to
//! incorporate the full [board representation][`Board`].

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

use crate::abs;
use crate::dice::DiceRoll;
use crate::board::{lemma_valid_implies_winnable, Board};

machine! {

machine Snakes refines abs::Abs {
    context: Board

    state {
        players: (int, int),
    }

    lift_context: |context| abs::Context {
        board_size: context.len(),
    }

    lift: |state| abs::Abs {
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

verus! {

/// The game is winnable from the next player's current square. Since no assumption is
/// made about state beyond validity and the invariant, every reachable state is winnable.
proof fn proof_winnable(board: Board, state: Snakes)
    requires
        board.valid(),
        Snakes::invariant(board, state),
    ensures
        board.can_win_from(state.players.0),
{
    lemma_valid_implies_winnable(board, state.players.0);
}

}

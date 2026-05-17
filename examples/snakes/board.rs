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

    valid(context) {
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
        // Board is winnable: every square other than the winning square has another square at most
        // 6 squares ahead that will permit forward progress. e.g. having 6 snakes in a row that
        // push you backwards would be an impenetrable barrier.
        &&& forall |i: int| #![trigger context.board[i]]
                0 <= i < context.board.len() - 1 ==> {
                    ||| i+1 + context.board[i+1] > i
                    ||| i+2 + context.board[i+2] > i
                    ||| i+3 + context.board[i+3] > i
                    ||| i+4 + context.board[i+4] > i
                    ||| i+5 + context.board[i+5] > i
                    ||| i+6 + context.board[i+6] > i
                }
        // Snakes and ladders cannot chain together
        &&& forall |i: int| #![trigger context.board[i]]
                0 <= i < context.board.len() && context.board[i] != 0 ==>
                    context.board[i + context.board[i]] == 0
    }

    state {
        player_positions: Seq<int>,
        next_player: int,
    }

    lift_context(context) {
        abs::Context {
            board_size: context.board.len(),
            player_count: context.player_count,
        }
    }

    lift(state) {
        abs::Abs {
            player_positions: state.player_positions,
            next_player: state.next_player,
        }
    }

    init(context) {
        player_positions: Seq::new(context.player_count, |i| { 0 }),
        next_player: 0,
    }

    invariant(context, state) {
        // Players can't sit at the top of a snake or the bottom of a ladder
        &&& forall |player: int| #![trigger state.player_positions[player]]
                0 <= player < state.player_positions.len() ==>
                    context.board[state.player_positions[player]] == 0
    }

    refined event Turn(roll: DiceRoll) {
        lift_in(context, state, roll) {
            state.take_turn(context, roll)
        }

        guard(context, state) {
            // Game not over
            &&& !state.lift().is_done(context.lift())
        }

        action(context, state) {
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
            let roll_pos = curr_pos + roll.value();
            if roll_pos >= context.board.len() {
                context.board.len() - 1
            } else {
                roll_pos + context.board[roll_pos]
            }
        }
    }
}
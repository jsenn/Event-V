use vstd::prelude::*;

use verus_machine::machine::*;
use verus_machine::verus_machine;

use crate::abs;
use crate::shared::DiceRoll;

verus_machine! {

machine Board refines abs::Abs {
    ctx {
        board: Seq<int>,
        player_count: nat,
    }

    valid(ctx) {
        // Someone is playing
        &&& ctx.player_count > 0
        // Board isn't degenerate (at least one turn to traverse)
        &&& ctx.board.len() > 1
        // Snakes and ladders can't take you off the board
        &&& forall |i: int| #![trigger ctx.board[i]]
                0 <= i < ctx.board.len() ==>
                    0 <= i + ctx.board[i] < ctx.board.len()
        // No snakes or ladders on first or last square
        &&& ctx.board[0] == 0 && ctx.board[ctx.board.len() - 1] == 0
        // Board is winnable: every square other than the winning square has another square at most
        // 6 squares ahead that will permit forward progress. e.g. having 6 snakes in a row that
        // push you backwards would be an impenetrable barrier.
        &&& forall |i: int| #![trigger ctx.board[i]]
                0 <= i < ctx.board.len() - 1 ==> {
                    ||| i+1 + ctx.board[i+1] > i
                    ||| i+2 + ctx.board[i+2] > i
                    ||| i+3 + ctx.board[i+3] > i
                    ||| i+4 + ctx.board[i+4] > i
                    ||| i+5 + ctx.board[i+5] > i
                    ||| i+6 + ctx.board[i+6] > i
                }
        // Snakes and ladders cannot chain together
        &&& forall |i: int| #![trigger ctx.board[i]]
                0 <= i < ctx.board.len() && ctx.board[i] != 0 ==>
                    ctx.board[i + ctx.board[i]] == 0
    }

    state {
        player_positions: Seq<int>,
        next_player: int,
    }

    lift_ctx(ctx) {
        abs::Ctx {
            board_size: ctx.board.len(),
            player_count: ctx.player_count,
        }
    }

    lift(state) {
        abs::Abs {
            player_positions: state.player_positions,
            next_player: state.next_player,
        }
    }

    init(ctx) {
        player_positions: Seq::new(ctx.player_count, |i| { 0 }),
        next_player: 0,
    }

    invariant(ctx, state) {
        // Players can't sit at the top of a snake or the bottom of a ladder
        &&& forall |player: int| #![trigger state.player_positions[player]]
                0 <= player < state.player_positions.len() ==>
                    ctx.board[state.player_positions[player]] == 0
    }

    refined event Turn(roll: DiceRoll) {
        lift_in(ctx, state, roll) {
            state.take_turn(ctx, roll)
        }

        guard(ctx, state) {
            // Game not over
            &&& !state.lift().is_done(ctx.lift())
        }

        action(ctx, state) {
            let next_pos = state.take_turn(ctx, roll);
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
        pub open spec fn take_turn(self, ctx: Ctx, roll: DiceRoll) -> int {
            let curr_pos = self.player_positions[self.next_player];
            let roll_pos = curr_pos + roll.value();
            if roll_pos >= ctx.board.len() {
                ctx.board.len() - 1
            } else {
                roll_pos + ctx.board[roll_pos]
            }
        }
    }
}
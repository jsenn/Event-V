use vstd::prelude::*;

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus_machine! {

machine Abs {
    ctx {
        board_size: nat,
        player_count: nat,
    }

    valid(ctx) {
        &&& ctx.board_size > 1
        &&& ctx.player_count > 0
    }

    state {
        player_positions: Seq<int>,
        next_player: int,
    }

    init(ctx) {
        player_positions: Seq::new(ctx.player_count, |i| { 0 }),
        next_player: 0,
    }

    invariant(ctx, state) {
        // Player count can't change
        &&& state.player_positions.len() == ctx.player_count
        // All players on the board
        &&& forall |i: int| #![trigger state.player_positions[i]]
            0 <= i < state.player_positions.len() ==>
                ctx.valid_position(state.player_positions[i])
        // At most one winner
        &&& forall |i: int, j: int| #![trigger state.player_positions[i], state.player_positions[j]]
            0 <= i < j < state.player_positions.len() ==>
                !(ctx.is_winner(state.player_positions[i]) && ctx.is_winner(state.player_positions[j]))
        // Next player valid
        &&& 0 <= state.next_player < state.player_positions.len()
    }

    event Turn(move_to: int) {
        guard(ctx, state) {
            // Game not over
            &&& !state.is_done(ctx)
            // Valid next position
            &&& ctx.valid_position(move_to)
        }

        action(ctx, state) {
            Abs {
                player_positions: state.move_player(state.next_player, move_to),
                next_player: state.advance_player(),
            }
        }
    }
}

}

verus! {

impl Abs {
    pub open spec fn valid_player(&self, idx: int) -> bool {
        0 <= idx < self.player_positions.len()
    }

    pub open spec fn is_done(&self, ctx: Ctx) -> bool {
        exists |player: int|
            #![trigger ctx.is_winner(self.player_positions[player])]
        {
            &&& self.valid_player(player)
            &&& ctx.is_winner(self.player_positions[player])
        }
    }

    pub open spec fn move_player(&self, player: int, move_to: int) -> Seq<int> {
        self.player_positions.update(player, move_to)
    }

    pub open spec fn advance_player(&self) -> int {
        if self.next_player + 1 == self.player_positions.len() {
            0
        } else {
            self.next_player + 1
        }
    }
}

impl Ctx {
    pub open spec fn valid_position(&self, pos: int) -> bool {
        0 <= pos < self.board_size
    }

    pub open spec fn is_winner(&self, pos: int) -> bool {
        pos == self.board_size - 1
    }
}

proof fn deadlock_free(ctx: Ctx, state: Abs)
    requires
        ctx.valid(),
        Abs::inv(ctx, state),
        !state.is_done(ctx),
    ensures
        exists |move_to: int| Turn::guard(ctx, state, move_to)
{
    assert(Turn::guard(ctx, state, 0));
}

}
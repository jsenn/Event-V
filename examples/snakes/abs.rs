use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Abs {
    context {
        board_size: nat,
        player_count: nat,
    }

    valid: |context| {
        &&& context.board_size > 1
        &&& context.player_count > 0
    }

    state {
        player_positions: Seq<int>,
        next_player: int,
    }

    init: |context| Abs {
        player_positions: Seq::new(context.player_count, |i| { 0 }),
        next_player: 0,
    }

    invariant: |context, state| {
        // Player count can't change
        &&& state.player_positions.len() == context.player_count
        // All players on the board
        &&& forall |i: int| #![trigger state.player_positions[i]]
            0 <= i < state.player_positions.len() ==>
                context.valid_position(state.player_positions[i])
        // At most one winner
        &&& forall |i: int, j: int| #![trigger state.player_positions[i], state.player_positions[j]]
            0 <= i < j < state.player_positions.len() ==>
                !(context.is_winner(state.player_positions[i]) && context.is_winner(state.player_positions[j]))
        // Next player valid
        &&& 0 <= state.next_player < state.player_positions.len()
    }

    event Turn(move_to: int) {
        guard: |context, state| {
            // Game not over
            &&& !state.is_done(context)
            // Valid next position
            &&& context.valid_position(move_to)
        }

        action: |context, state| Abs {
            player_positions: state.move_player(state.next_player, move_to),
            next_player: state.advance_player(),
        }
    }
}

}

verus! {

impl Abs {
    pub open spec fn valid_player(&self, idx: int) -> bool {
        0 <= idx < self.player_positions.len()
    }

    pub open spec fn is_done(&self, context: Context) -> bool {
        exists |player: int|
            #![trigger context.is_winner(self.player_positions[player])]
        {
            &&& self.valid_player(player)
            &&& context.is_winner(self.player_positions[player])
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

impl Context {
    pub open spec fn valid_position(&self, pos: int) -> bool {
        0 <= pos < self.board_size
    }

    pub open spec fn is_winner(&self, pos: int) -> bool {
        pos == self.board_size - 1
    }
}

proof fn deadlock_free(context: Context, state: Abs)
    requires
        context.valid(),
        Abs::invariant(context, state),
        !state.is_done(context),
    ensures
        exists |move_to: int| Turn::guard(context, state, move_to)
{
    assert(Turn::guard(context, state, 0));
}

}

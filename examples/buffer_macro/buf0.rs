use vstd::prelude::*;

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus_machine! {

deadlock_free machine Buf0 {
    ctx {
        max_size: nat,
    }

    valid(ctx) {
        ctx.max_size > 0
    }

    state {
        size: nat,
    }

    init(ctx) {
        size: 0
    }

    invariant(ctx, state) {
        state.size <= ctx.max_size
    }

    event Put {
        guard(ctx, state) {
            state.size < ctx.max_size
        }

        action(ctx, state) {
            Buf0 {
                size: state.size + 1,
            }
        }
    }

    event Fetch {
        guard(ctx, state) {
            state.size > 0
        }

        action(ctx, state) {
            Buf0 {
                size: (state.size - 1) as nat,
            }
        }
    }

    event GetSize -> nat {
        guard(ctx, state) {
            true
        }

        action(ctx, state) {
            state
        }

        output(ctx, state) {
            state.size
        }
    }
}

}

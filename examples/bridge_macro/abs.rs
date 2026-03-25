use vstd::prelude::*;

use verus_machine::machine::*;
use verus_machine::verus_machine;
use crate::shared::*;

verus_machine! {

deadlock_free machine Abs {
    ctx: BridgeCtx,

    state {
        cars: nat,
    }

    init(ctx) {
        cars: 0
    }

    invariant(ctx, state) {
        state.cars <= ctx.max_cars
    }

    event MainlandIn {
        guard(ctx, state) {
            state.cars > 0
        }

        action(ctx, state) {
            Abs {
                cars: (state.cars - 1) as nat,
                ..state
            }
        }
    }

    event MainlandOut {
        guard(ctx, state) {
            state.cars < ctx.max_cars
        }

        action(ctx, state) {
            Abs {
                cars: state.cars + 1,
                ..state
            }
        }
    }
}

}

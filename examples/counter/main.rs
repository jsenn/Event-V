use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Counter {
    ctx {
        max_value: nat,
    }

    valid(ctx) {
        // A counter with `max_value == 0` could never be incremented or decremented, which would
        // be quite boring
        ctx.max_value > 0
    }

    state {
        value: nat,
    }

    init(ctx) {
        value: 0
    }

    invariant(ctx, state) {
        state.value <= ctx.max_value
    }

    // The machine's first event increments the counter by 1. It may only fire if the current value
    // is less than the max value.
    event Increment {
        // We may only increment a counter whose value is less than the max value.
        guard(ctx, state) {
            state.value < ctx.max_value
        }

        action(ctx, state) {
            Counter {
                value: state.value + 1,
            }
        }
    }

    event Decrement {
        // We may only decrement a counter if its value is greater than zero.
        guard(ctx, state) {
            state.value > 0
        }

        action(ctx, state) {
            Counter {
                value: (state.value - 1) as nat,
            }
        }
    }
}

}

fn main() {}
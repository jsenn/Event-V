use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Counter {
    context {
        max_value: nat,
    }

    valid: |context| {
        // A counter with `max_value == 0` could never be incremented or decremented, which would
        // be quite boring
        context.max_value > 0
    }

    state {
        value: nat,
    }

    init: |context| Counter { value: 0 },

    invariant: |context, state| state.value <= context.max_value,

    // The machine's first event increments the counter by 1. It may only fire if the current value
    // is less than the max value.
    event Increment {
        // We may only increment a counter whose value is less than the max value.
        guard: |context, state| state.value < context.max_value,
        action: |context, state| Counter { value: state.value + 1 },
    }

    event Decrement {
        // We may only decrement a counter if its value is greater than zero.
        guard: |context, state| state.value > 0,
        action: |context, state| Counter { value: (state.value - 1) as nat },
    }
}

}

fn main() {}

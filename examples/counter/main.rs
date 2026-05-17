use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Counter {
    // Declare the **context** struct for the machine. This contains configuration that does not
    // change through the machine's lifetime.
    context {
        max_value: nat,
    }

    // A counter with `max_value == 0` could never be incremented or decremented, which would
    // be quite boring
    valid: |context| context.max_value > 0

    // Declare the **state** struct. Unlike the context, the state can be changed by events.
    // The state takes the name of the machine, so in this case we will end up with a
    // `struct Counter { pub value: nat }`.
    state {
        value: nat,
    }

    // This machine has a single **initialization event**, which sets the counter's value to 0.
    init: |context| Counter { value: 0 }

    // Every machine has an **invariant** that determines whether it is in a valid state or not.
    // For our counter machine, the invariant is that the value does not exceed the configured
    // `max_value`. Note that because the value is declared as `nat`, it must also be non-negative,
    // but we don't have to explicitly add that in the invariant.
    invariant: |context, state| state.value <= context.max_value

    // The machine's first event increments the counter by 1. It may only fire if the current value
    // is less than the max value.
    event Increment {
        // An event's **guard** determines when it is valid for the event to fire. In this case, we
        // may only increment a counter whose value is less than the max value.
        guard: |context, state| state.value < context.max_value

        // The **action** for an event defines how the machine's state changes after the event
        // fires. In this case, the post-action state has its value incremented by 1.
        action: |context, state| Counter { value: state.value + 1 }
    }

    // The Decrement event is similar in structure to Increment, except that its guard requires
    // that the current value be greater than zero.
    event Decrement {
        guard: |context, state| state.value > 0

        // Subtracting two `nat`s produces an `int` in Verus, so we cast the result with `as nat`.
        action: |context, state| Counter { value: (state.value - 1) as nat }
    }
}

}

fn main() {}

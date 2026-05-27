//! Here we define the most abstract model of the bridge controller. At this level, we ignore the
//! bridge completely. The only thing we track is the total number of cars that are on *either* the
//! bridge or the island.
//! 
//! We define two events: [`MainlandIn`], which represents a car entering the mainland from the
//! bridge, and [`MainlandOut`], which represents a car leaving the mainland for the island.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

deadlock_free machine Abs {
    context {
        max_cars: nat,
    }

    valid: |context| context.max_cars > 0

    state {
        cars: nat,
    }

    init: |context| Abs { cars: 0 }

    invariant: |context, state| state.cars <= context.max_cars

    event MainlandIn {
        guard: |context, state| state.cars > 0
        action: |context, state| Abs {
            cars: (state.cars - 1) as nat,
            ..state
        }
    }

    event MainlandOut {
        guard: |context, state| state.cars < context.max_cars
        action: |context, state| Abs {
            cars: state.cars + 1,
            ..state
        }
    }
}

}

//! Here we refine the [abstract model][`abs::Abs`] by adding the bridge itself. Instead of having
//! a count of the total cars on the island and bridge considered as one, we track the number on
//! the bridge heading to the island, the number on the island, and the number coming back to the
//! mainland on the bridge.
//! 
//! We also introduce the constraint that the bridge is one-way.

use vstd::prelude::*;

use crate::abs;

use event_v::machine::*;
use event_v::machine;

machine! {

deadlock_free machine Ref1 refines abs::Abs {
    context: abs::Context,

    state {
        cars_to_island: nat,
        cars_on_island: nat,
        cars_to_mainland: nat,
    }

    init: |context| Ref1 {
        cars_to_island: 0,
        cars_on_island: 0,
        cars_to_mainland: 0,
    }

    lift: |state| abs::Abs { cars: state.total_cars() }

    // The bridge is one-way: cars may be travelling to the island or from it, but not both simultaneously.
    invariant: |context, state| {
        ||| state.cars_to_island == 0
        ||| state.cars_to_mainland == 0
    }

    // There are 2 new events: `IslandIn` and `IslandOut`. The former reduces this variant by
    // moving a car from the bridge to the island. Since the on-island count comes second, the
    // variant is lexicographically smaller. The latter event reduces it by reducing the number of
    // cars on the island.
    variant: |context, state| -> (nat, nat) {
        (state.cars_to_island, state.cars_on_island)
    }

    refined event MainlandIn {
        guard: |context, state| state.cars_to_mainland > 0
        action: |context, state| Ref1 {
            cars_to_mainland: (state.cars_to_mainland - 1) as nat,
            ..state
        }
    }

    refined event MainlandOut {
        guard: |context, state| {
            &&& state.cars_to_mainland == 0 // one-way
            &&& state.total_cars() < context.max_cars // capacity
        }
        action: |context, state| Ref1 {
            cars_to_island: state.cars_to_island + 1,
            ..state
        }
    }

    concrete event IslandIn {
        guard: |context, state| state.cars_to_island > 0
        action: |context, state| Ref1 {
            cars_to_island: (state.cars_to_island - 1) as nat,
            cars_on_island: state.cars_on_island + 1,
            ..state
        }
    }

    concrete event IslandOut {
        guard: |context, state| {
            &&& state.cars_on_island > 0
            &&& state.cars_to_island == 0 // one-way
        }
        action: |context, state| Ref1 {
            cars_on_island: (state.cars_on_island - 1) as nat,
            cars_to_mainland: state.cars_to_mainland + 1,
            ..state
        }
    }
}

}

verus! {

impl Ref1 {
    pub open spec fn total_cars(self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }
}

}

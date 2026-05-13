use vstd::prelude::*;

use crate::abs;

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus_machine! {

deadlock_free machine Ref1 refines abs::Abs {
    ctx: abs::Ctx,

    state {
        cars_to_island: nat,
        cars_on_island: nat,
        cars_to_mainland: nat,
    }

    init(ctx) {
        cars_to_island: 0,
        cars_on_island: 0,
        cars_to_mainland: 0
    }

    lift(state) {
        abs::Abs {
            cars: state.total_cars(),
        }
    }

    invariant(ctx, state) {
        ||| state.cars_to_island == 0
        ||| state.cars_to_mainland == 0
    }

    variant(ctx, state) -> (nat, nat) {
        (state.cars_to_island, state.cars_on_island)
    }

    refined event MainlandIn {
        guard(ctx, state) {
            state.cars_to_mainland > 0
        }

        action(ctx, state) {
            Ref1 {
                cars_to_mainland: (state.cars_to_mainland - 1) as nat,
                ..state
            }
        }
    }

    refined event MainlandOut {
        guard(ctx, state) {
            &&& state.cars_to_mainland == 0
            &&& state.total_cars() < ctx.max_cars
        }

        action(ctx, state) {
            Ref1 {
                cars_to_island: state.cars_to_island + 1,
                ..state
            }
        }
    }

    concrete event IslandIn {
        guard(ctx, state) {
            state.cars_to_island > 0
        }

        action(ctx, state) {
            Ref1 {
                cars_to_island: (state.cars_to_island - 1) as nat,
                cars_on_island: state.cars_on_island + 1,
                ..state
            }
        }
    }

    concrete event IslandOut {
        guard(ctx, state) {
            &&& state.cars_on_island > 0
            &&& state.cars_to_island == 0
        }

        action(ctx, state) {
            Ref1 {
                cars_on_island: (state.cars_on_island - 1) as nat,
                cars_to_mainland: state.cars_to_mainland + 1,
                ..state
            }
        }
    }
}

}

verus! {

impl Ref1 {
    pub open spec fn total_cars(&self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }
}

}

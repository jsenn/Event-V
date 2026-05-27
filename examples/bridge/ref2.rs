//! Here we refine the model further to include traffic lights at each end of the bridge. Cars are
//! assumed to obey the traffic lights. At this level, the traffic lights can magically sense the
//! number of cars on the bridge and the island.
//! 
//! We introduce the new events [`TurnGreenIsland`] and [`TurnGreenMainland`] which toggle the
//! lights.

use vstd::prelude::*;

use crate::abs;
use crate::ref1;

use crate::shared::TrafficLight;

use event_v::machine::*;
use event_v::machine;

machine! {

deadlock_free machine Ref2 refines ref1::Ref1 {
    context: abs::Context,

    state {
        cars_to_island: nat,
        cars_on_island: nat,
        cars_to_mainland: nat,

        light_mainland: TrafficLight,
        light_island: TrafficLight,

        // These flags are needed to prevent toggling the light before a car on the other side has
        // had a chance to enter the bridge.
        car_left_mainland: bool,
        car_left_island: bool,
    }

    init: |context| Ref2 {
        cars_to_island: 0,
        cars_on_island: 0,
        cars_to_mainland: 0,

        // Initially the mainland side's light is green. Otherwise, no one could ever enter the
        // island!
        light_mainland: TrafficLight::Green,
        light_island: TrafficLight::Red,

        car_left_mainland: false,
        // Note that we set `car_left_island`. The naming is unfortunate in this case as no car
        // has done anything yet, but we need it to satisfy the invariant.
        car_left_island: true,
    }

    lift: |state| ref1::Ref1 {
        cars_to_island: state.cars_to_island,
        cars_on_island: state.cars_on_island,
        cars_to_mainland: state.cars_to_mainland,
    }

    invariant: |context, state| {
        // Only turn mainland green if one-way and capacity constraints are satisfied
        &&& self.light_mainland.is_green() ==> {
            &&& self.cars_to_mainland == 0
            &&& self.lift().total_cars() < context.max_cars
        }
        // Only turn island green if one-way constraint is satisfied and someone is actually there
        &&& self.light_island.is_green() ==> self.cars_to_island == 0 && self.cars_on_island > 0
        // Both lights can't be green
        &&& self.light_mainland.is_red() || self.light_island.is_red()
        // Car left flags
        &&& self.light_mainland.is_red() ==> self.car_left_mainland
        &&& self.light_island.is_red() ==> self.car_left_island
    }

    variant: |context, state| -> (bool, bool) {
        (state.car_left_island, state.car_left_mainland)
    }

    refined event MainlandIn {
        guard: |context, state| state.cars_to_mainland > 0
        action: |context, state| Ref2 {
            cars_to_mainland: (state.cars_to_mainland - 1) as nat,
            ..state
        }
    }

    refined event MainlandOut {
        guard: |context, state| state.light_mainland.is_green()
        action: |context, state| Ref2 {
            cars_to_island: state.cars_to_island + 1,
            light_mainland:
                // Last one out toggles the light
                if state.cars_to_island + state.cars_on_island + 1 == context.max_cars {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
            car_left_mainland: true,
            ..state
        }
    }

    refined event IslandIn {
        guard: |context, state| state.cars_to_island > 0
        action: |context, state| Ref2 {
            cars_to_island: (state.cars_to_island - 1) as nat,
            cars_on_island: state.cars_on_island + 1,
            ..state
        }
    }

    refined event IslandOut {
        guard: |context, state| state.light_island.is_green()
        action: |context, state| Ref2 {
            cars_on_island: (state.cars_on_island - 1) as nat,
            cars_to_mainland: state.cars_to_mainland + 1,
            light_island:
                // Last one out toggles the light
                if state.cars_on_island == 1 {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
            car_left_island: true,
            ..state
        }
    }

    concrete event TurnGreenMainland {
        guard: |context, state| {
            &&& state.light_mainland.is_red()
            &&& state.car_left_island
            &&& state.lift().total_cars() < context.max_cars
            &&& state.cars_to_mainland == 0
        }
        action: |context, state| Ref2 {
            light_mainland: TrafficLight::Green,
            light_island: TrafficLight::Red,
            car_left_mainland: false,
            ..state
        }
    }

    concrete event TurnGreenIsland {
        guard: |context, state| {
            &&& state.light_island.is_red()
            &&& state.car_left_mainland
            &&& state.cars_on_island > 0
            &&& state.cars_to_island == 0
        }
        action: |context, state| Ref2 {
            light_island: TrafficLight::Green,
            light_mainland: TrafficLight::Red,
            car_left_island: false,
            ..state
        }
    }
}

}

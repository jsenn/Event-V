//! In all previous refinements, facts about the environment (like car counts) were mixed with
//! the bridge controller logic. For example, traffic lights toggled themselves when car counts
//! changed.
//! 
//! Here, we remove most of the magic. The environment's state is separated from the controller's.
//! The controller turns traffic lights on and off by reacting to signals sent by the environment
//! through sensors.
//! 
//! Note that there is still a slight conflation of controller state and environment state with the
//! traffic lights.

use vstd::prelude::*;

use crate::abs;
use crate::ref2;

use crate::shared::TrafficLight;

use event_v::machine::*;
use event_v::machine;

verus! {

/// A state set on the bridge controller by the pressure sensors.
pub enum Flag {
    Set,
    Clear,
}

impl Flag {
    pub open spec fn is_set(self) -> bool {
        matches!(self, Flag::Set)
    }

    pub open spec fn is_clear(self) -> bool {
        matches!(self, Flag::Clear)
    }
}

/// Indicates the state of a car pressure sensor.
pub enum Sensor {
    /// Indicates that a car is sitting on the sensor
    On,
    /// Indicates that a car is not sitting on the sensor
    Off,
}

impl Sensor {
    pub open spec fn is_on(self) -> bool {
        matches!(self, Sensor::On)
    }

    pub open spec fn is_off(self) -> bool {
        matches!(self, Sensor::Off)
    }
}
/// Holds the internal state of the bridge controller. The environment communicates with the
/// controller by setting various [`Flag`]s, which the controller can then react to.
pub struct Controller {
    /// Flag set by [`Environment::sensor_mainland_in`]
    pub flag_entered_mainland: Flag,
    /// Flag set by [`Environment::sensor_mainland_out`]
    pub flag_left_mainland: Flag,
    /// Flag set by [`Environment::sensor_island_in`]
    pub flag_entered_island: Flag,
    /// Flag set by [`Environment::sensor_island_out`]
    pub flag_left_island: Flag,

    /// Controls the mainland traffic light
    pub light_mainland: TrafficLight,
    /// Controls the island traffic light
    pub light_island: TrafficLight,

    /// The controller's internal count of the number of cars on the bridge heading to the island
    pub cars_to_island: nat,
    /// The controller's internal count of the number of cars on the island
    pub cars_on_island: nat,
    /// The controller's internal count of the number of cars on the bridge heading to the mainland
    pub cars_to_mainland: nat,

    /// Indicates that a car has left the mainland, so it is safe to toggle the light
    pub car_left_mainland: bool,
    /// Indicates that a car has left the island, so it is safe to toggle the light
    pub car_left_island: bool,
}

impl Controller {
    pub open spec fn total_cars(self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }
}

/// Represents the true state of the world outside the controller.
pub struct Environment {
    /// The actual number of cars on the bridge head toward the island
    pub cars_to_island: nat,
    /// The actual number of cars on the island
    pub cars_on_island: nat,
    /// The actual number of cars on the bridge head toward the mainland
    pub cars_to_mainland: nat,

    /// The state of the pressure sensor that detects cars leaving the bridge for the mainland
    pub sensor_mainland_in: Sensor,
    /// The state of the pressure sensor that detects cars leaving the mainland for the bridge
    pub sensor_mainland_out: Sensor,
    /// The state of the pressure sensor that detects cars leaving the bridge for the island
    pub sensor_island_in: Sensor,
    /// The state of the pressure sensor that detects cars leaving the island for the bridge
    pub sensor_island_out: Sensor,
}

}

machine! {

deadlock_free machine Ref3 refines ref2::Ref2 {
    context: abs::Context,

    state {
        con: Controller,
        env: Environment,
    }

    init: |context| Ref3 {
        con: Controller {
            flag_entered_mainland: Flag::Clear,
            flag_left_mainland: Flag::Clear,
            flag_entered_island: Flag::Clear,
            flag_left_island: Flag::Clear,

            light_mainland: TrafficLight::Green,
            light_island: TrafficLight::Red,

            cars_to_island: 0,
            cars_on_island: 0,
            cars_to_mainland: 0,

            car_left_mainland: false,
            car_left_island: true,
        },
        env: Environment {
            cars_to_island: 0,
            cars_on_island: 0,
            cars_to_mainland: 0,

            sensor_mainland_in: Sensor::Off,
            sensor_mainland_out: Sensor::Off,
            sensor_island_in: Sensor::Off,
            sensor_island_out: Sensor::Off,
        },
    }

    lift: |state| ref2::Ref2 {
        cars_to_island: state.con.cars_to_island,
        cars_on_island: state.con.cars_on_island,
        cars_to_mainland: state.con.cars_to_mainland,

        light_mainland: state.con.light_mainland,
        light_island: state.con.light_island,

        car_left_mainland: state.con.car_left_mainland,
        car_left_island: state.con.car_left_island,
    }

    invariant: |context, state| {
        // Sensors detect the presence of physical cars
        &&& self.env.sensor_island_in.is_on() ==> self.env.cars_to_island > 0
        &&& self.env.sensor_island_out.is_on() ==> self.env.cars_on_island > 0
        &&& self.env.sensor_mainland_in.is_on() ==> self.env.cars_to_mainland > 0
        // Cars obey traffic lights
        &&& self.con.flag_left_mainland.is_set() ==> self.con.light_mainland.is_green()
        &&& self.con.flag_left_island.is_set() ==> self.con.light_island.is_green()
        // Sensors set controller flags appropriately
        &&& self.env.sensor_island_in.is_on() ==> self.con.flag_entered_island.is_clear()
        &&& self.env.sensor_island_out.is_on() ==> self.con.flag_left_island.is_clear()
        &&& self.env.sensor_mainland_in.is_on() ==> self.con.flag_entered_mainland.is_clear()
        &&& self.env.sensor_mainland_out.is_on() ==> self.con.flag_left_mainland.is_clear()
        // Controller tracks cars on bridge toward island correctly
        &&& self.con.flag_entered_island.is_set() && self.con.flag_left_mainland.is_set()
            ==> self.env.cars_to_island == self.con.cars_to_island
        &&& self.con.flag_entered_island.is_clear() && self.con.flag_left_mainland.is_set()
            ==> self.env.cars_to_island == self.con.cars_to_island + 1
        &&& self.con.flag_entered_island.is_set() && self.con.flag_left_mainland.is_clear()
            ==> self.env.cars_to_island == self.con.cars_to_island - 1
        &&& self.con.flag_entered_island.is_clear() && self.con.flag_left_mainland.is_clear()
            ==> self.env.cars_to_island == self.con.cars_to_island
        // Controller tracks cars on island correctly
        &&& self.con.flag_entered_island.is_set() && self.con.flag_left_island.is_set()
            ==> self.env.cars_on_island == self.con.cars_on_island
        &&& self.con.flag_entered_island.is_clear() && self.con.flag_left_island.is_set()
            ==> self.env.cars_on_island == self.con.cars_on_island - 1
        &&& self.con.flag_entered_island.is_set() && self.con.flag_left_island.is_clear()
            ==> self.env.cars_on_island == self.con.cars_on_island + 1
        &&& self.con.flag_entered_island.is_clear() && self.con.flag_left_island.is_clear()
            ==> self.env.cars_on_island == self.con.cars_on_island
        // Controller tracks cars on bridge toward mainland correctly
        &&& self.con.flag_left_island.is_set() && self.con.flag_entered_mainland.is_set()
            ==> self.env.cars_to_mainland == self.con.cars_to_mainland
        &&& self.con.flag_left_island.is_clear() && self.con.flag_entered_mainland.is_set()
            ==> self.env.cars_to_mainland == self.con.cars_to_mainland - 1
        &&& self.con.flag_left_island.is_set() && self.con.flag_entered_mainland.is_clear()
            ==> self.env.cars_to_mainland == self.con.cars_to_mainland + 1
        &&& self.con.flag_left_island.is_clear() && self.con.flag_entered_mainland.is_clear()
            ==> self.env.cars_to_mainland == self.con.cars_to_mainland
        // Cars are only travelling along the bridge in one direction at a time
        &&& self.env.cars_to_island == 0 || self.env.cars_to_mainland == 0
        // The physical number of cars in the system is capped
        &&& self.env.cars_to_island + self.env.cars_on_island + self.env.cars_to_mainland <= context.max_cars
    }

    variant: |context, state| -> (bool, bool, bool, bool, bool, bool, bool, bool) {
        (
            state.con.flag_left_mainland.is_clear(),
            state.con.flag_entered_mainland.is_clear(),
            state.con.flag_left_island.is_clear(),
            state.con.flag_entered_island.is_clear(),
            state.env.sensor_mainland_out.is_off(),
            state.env.sensor_mainland_in.is_off(),
            state.env.sensor_island_out.is_off(),
            state.env.sensor_island_in.is_off(),
        )
    }

    // Update the controller when sensors indicate a car has entered the mainland from the bridge.
    refined event MainlandIn {
        guard: |context, state| {
            &&& state.con.flag_entered_mainland.is_set()
            &&& state.con.cars_to_mainland > 0
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_entered_mainland: Flag::Clear,
                cars_to_mainland: (state.con.cars_to_mainland - 1) as nat,
                ..state.con
            },
            ..state
        }
    }

    // Update the controller when sensors indicate that a car has entered the bridge from the
    // mainland.
    refined event MainlandOut {
        guard: |context, state| {
            &&& state.con.flag_left_mainland.is_set()
            &&& state.con.total_cars() + 1 <= context.max_cars
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_left_mainland: Flag::Clear,
                cars_to_island: state.con.cars_to_island + 1,
                light_mainland: if state.con.total_cars() + 1 == context.max_cars {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
                car_left_mainland: true,
                ..state.con
            },
            ..state
        }
    }

    // Update the controller when sensors indicate that a car has entered the island from the
    // bridge.
    refined event IslandIn {
        guard: |context, state| {
            &&& state.con.flag_entered_island.is_set()
            &&& state.con.cars_to_island > 0
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_entered_island: Flag::Clear,
                cars_to_island: (state.con.cars_to_island - 1) as nat,
                cars_on_island: state.con.cars_on_island + 1,
                ..state.con
            },
            ..state
        }
    }

    // Update the controller when sensors indicate that a car has entered the bridge from the
    // island.
    refined event IslandOut {
        guard: |context, state| {
            &&& state.con.flag_left_island.is_set()
            &&& state.con.cars_on_island > 0
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_left_island: Flag::Clear,
                cars_on_island: (state.con.cars_on_island - 1) as nat,
                cars_to_mainland: state.con.cars_to_mainland + 1,
                light_island: if state.con.cars_on_island == 1 {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
                car_left_island: true,
                ..state.con
            },
            ..state
        }
    }

    refined event TurnGreenMainland {
        guard: |context, state| {
            &&& state.con.light_mainland.is_red()
            &&& state.con.car_left_island
            &&& state.con.flag_left_island.is_clear()
            &&& state.con.cars_to_mainland == 0
            &&& state.con.total_cars() < context.max_cars
        }
        action: |context, state| Ref3 {
            con: Controller {
                light_mainland: TrafficLight::Green,
                light_island: TrafficLight::Red,
                car_left_mainland: false,
                ..state.con
            },
            ..state
        }
    }

    refined event TurnGreenIsland {
        guard: |context, state| {
            &&& state.con.light_island.is_red()
            &&& state.con.car_left_mainland
            &&& state.con.flag_left_mainland.is_clear()
            &&& state.con.cars_on_island > 0
            &&& state.con.cars_to_island == 0
        }
        action: |context, state| Ref3 {
            con: Controller {
                light_island: TrafficLight::Green,
                light_mainland: TrafficLight::Red,
                car_left_island: false,
                ..state.con
            },
            ..state
        }
    }

    // Car arrives at the mainland->bridge pressure sensor
    concrete event SensorMainlandOutArrive {
        guard: |context, state| {
            &&& state.env.sensor_mainland_out.is_off()
            &&& state.con.flag_left_mainland.is_clear()
        }
        action: |context, state| Ref3 {
            env: Environment {
                sensor_mainland_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    // Car arrives at the bridge->mainland pressure sensor
    concrete event SensorMainlandInArrive {
        guard: |context, state| {
            &&& state.env.sensor_mainland_in.is_off()
            &&& state.con.flag_entered_mainland.is_clear()
            &&& state.env.cars_to_mainland > 0
        }
        action: |context, state| Ref3 {
            env: Environment {
                sensor_mainland_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    // Car arrives at the island->bridge pressure sensor
    concrete event SensorIslandOutArrive {
        guard: |context, state| {
            &&& state.env.cars_on_island > 0
            &&& state.env.sensor_island_out.is_off()
            &&& state.con.flag_left_island.is_clear()
        }
        action: |context, state| Ref3 {
            env: Environment {
                sensor_island_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    // Car arrives at the bridge->island pressure sensor
    concrete event SensorIslandInArrive {
        guard: |context, state| {
            &&& state.env.cars_to_island > 0
            &&& state.env.sensor_island_in.is_off()
            &&& state.con.flag_entered_island.is_clear()
        }
        action: |context, state| Ref3 {
            env: Environment {
                sensor_island_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    // Car leaves mainland->bridge pressure sensor
    concrete event SensorMainlandOutDepart {
        guard: |context, state| {
            &&& state.env.sensor_mainland_out.is_on()
            &&& state.con.light_mainland.is_green()
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_left_mainland: Flag::Set,
                ..state.con
            },
            env: Environment {
                sensor_mainland_out: Sensor::Off,
                cars_to_island: state.env.cars_to_island + 1,
                ..state.env
            },
            ..state
        }
    }

    // Car leaves bridge->mainland pressure sensor
    concrete event SensorMainlandInDepart {
        guard: |context, state| state.env.sensor_mainland_in.is_on()
        action: |context, state| Ref3 {
            con: Controller {
                flag_entered_mainland: Flag::Set,
                ..state.con
            },
            env: Environment {
                sensor_mainland_in: Sensor::Off,
                cars_to_mainland: (state.env.cars_to_mainland - 1) as nat,
                ..state.env
            },
            ..state
        }
    }

    // Car leaves island->bridge pressure sensor
    concrete event SensorIslandOutDepart {
        guard: |context, state| {
            &&& state.env.sensor_island_out.is_on()
            &&& state.con.light_island.is_green()
        }
        action: |context, state| Ref3 {
            con: Controller {
                flag_left_island: Flag::Set,
                ..state.con
            },
            env: Environment {
                sensor_island_out: Sensor::Off,
                cars_on_island: (state.env.cars_on_island - 1) as nat,
                cars_to_mainland: state.env.cars_to_mainland + 1,
                ..state.env
            },
            ..state
        }
    }

    // Car leaves bridge->island pressure sensor
    concrete event SensorIslandInDepart {
        guard: |context, state| state.env.sensor_island_in.is_on()
        action: |context, state| Ref3 {
            con: Controller {
                flag_entered_island: Flag::Set,
                ..state.con
            },
            env: Environment {
                sensor_island_in: Sensor::Off,
                cars_to_island: (state.env.cars_to_island - 1) as nat,
                cars_on_island: state.env.cars_on_island + 1,
                ..state.env
            },
            ..state
        }
    }
}

}


use vstd::prelude::*;

use crate::abs;
use crate::ref2;

use crate::shared::{Flag, Sensor, TrafficLight};

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus! {
pub struct Controller {
    pub flag_entered_mainland: Flag,
    pub flag_left_mainland: Flag,
    pub flag_entered_island: Flag,
    pub flag_left_island: Flag,

    pub light_mainland: TrafficLight,
    pub light_island: TrafficLight,

    pub cars_to_island: nat,
    pub cars_on_island: nat,
    pub cars_to_mainland: nat,

    pub car_left_mainland: bool,
    pub car_left_island: bool,
}

impl Controller {
    pub open spec fn total_cars(&self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }
}

pub struct Environment {
    pub cars_to_island: nat,
    pub cars_on_island: nat,
    pub cars_to_mainland: nat,

    pub sensor_mainland_in: Sensor,
    pub sensor_mainland_out: Sensor,
    pub sensor_island_in: Sensor,
    pub sensor_island_out: Sensor,
}

}

verus_machine! {

deadlock_free machine Ref3 refines ref2::Ref2 {
    ctx: abs::Ctx,

    state {
        con: Controller,
        env: Environment,
    }

    init(ctx) {
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

    lift(state) {
        ref2::Ref2 {
            cars_to_island: self.con.cars_to_island,
            cars_on_island: self.con.cars_on_island,
            cars_to_mainland: self.con.cars_to_mainland,

            light_mainland: self.con.light_mainland,
            light_island: self.con.light_island,

            car_left_mainland: self.con.car_left_mainland,
            car_left_island: self.con.car_left_island,
        }
    }

    invariant(ctx, state) {
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
        &&& self.env.cars_to_island + self.env.cars_on_island + self.env.cars_to_mainland <= ctx.max_cars
    }

    variant(ctx, state) -> (bool, bool, bool, bool, bool, bool, bool, bool) {
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

    refined event MainlandIn {
        guard(ctx, state) {
            &&& state.con.flag_entered_mainland.is_set()
            &&& state.con.cars_to_mainland > 0
        }

        action(ctx, state) {
            Ref3 {
                con: Controller {
                    flag_entered_mainland: Flag::Clear,
                    cars_to_mainland: (state.con.cars_to_mainland - 1) as nat,
                    ..state.con
                },
                ..state
            }
        }
    }

    refined event MainlandOut {
        guard(ctx, state) {
            &&& state.con.flag_left_mainland.is_set()
            &&& state.con.total_cars() + 1 <= ctx.max_cars
        }

        action(ctx, state) {
            Ref3 {
                con: Controller {
                    flag_left_mainland: Flag::Clear,
                    cars_to_island: state.con.cars_to_island + 1,
                    light_mainland: if state.con.total_cars() + 1 == ctx.max_cars {
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
    }

    refined event IslandIn {
        guard(ctx, state) {
            &&& state.con.flag_entered_island.is_set()
            &&& state.con.cars_to_island > 0
        }

        action(ctx, state) {
            Ref3 {
                con: Controller {
                    flag_entered_island: Flag::Clear,
                    cars_to_island: (state.con.cars_to_island - 1) as nat,
                    cars_on_island: state.con.cars_on_island + 1,
                    ..state.con
                },
                ..state
            }
        }
    }

    refined event IslandOut {
        guard(ctx, state) {
            &&& state.con.flag_left_island.is_set()
            &&& state.con.cars_on_island > 0
        }

        action(ctx, state) {
            Ref3 {
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
    }

    refined event TurnGreenMainland {
        guard(ctx, state) {
            &&& state.con.light_mainland.is_red()
            &&& state.con.car_left_island
            &&& state.con.flag_left_island.is_clear()
            &&& state.con.cars_to_mainland == 0
            &&& state.con.total_cars() < ctx.max_cars
        }

        action(ctx, state) {
            Ref3 {
                con: Controller {
                    light_mainland: TrafficLight::Green,
                    light_island: TrafficLight::Red,
                    car_left_mainland: false,
                    ..state.con
                },
                ..state
            }
        }
    }

    refined event TurnGreenIsland {
        guard(ctx, state) {
            &&& state.con.light_island.is_red()
            &&& state.con.car_left_mainland
            &&& state.con.flag_left_mainland.is_clear()
            &&& state.con.cars_on_island > 0
            &&& state.con.cars_to_island == 0
        }

        action(ctx, state) {
            Ref3 {
                con: Controller {
                    light_island: TrafficLight::Green,
                    light_mainland: TrafficLight::Red,
                    car_left_island: false,
                    ..state.con
                },
                ..state
            }
        }
    }

    concrete event SensorMainlandOutArrive {
        guard(ctx, state) {
            &&& state.env.sensor_mainland_out.is_off()
            &&& state.con.flag_left_mainland.is_clear()
        }

        action(ctx, state) {
            Ref3 {
                env: Environment {
                    sensor_mainland_out: Sensor::On,
                    ..state.env
                },
                ..state
            }
        }

    }

    concrete event SensorMainlandInArrive {
        guard(ctx, state) {
            &&& state.env.sensor_mainland_in.is_off()
            &&& state.con.flag_entered_mainland.is_clear()
            &&& state.env.cars_to_mainland > 0
        }

        action(ctx, state) {
            Ref3 {
                env: Environment {
                    sensor_mainland_in: Sensor::On,
                    ..state.env
                },
                ..state
            }
        }

    }

    concrete event SensorIslandOutArrive {
        guard(ctx, state) {
            &&& state.env.cars_on_island > 0
            &&& state.env.sensor_island_out.is_off()
            &&& state.con.flag_left_island.is_clear()
        }

        action(ctx, state) {
            Ref3 {
                env: Environment {
                    sensor_island_out: Sensor::On,
                    ..state.env
                },
                ..state
            }
        }

    }

    concrete event SensorIslandInArrive {
        guard(ctx, state) {
            &&& state.env.cars_to_island > 0
            &&& state.env.sensor_island_in.is_off()
            &&& state.con.flag_entered_island.is_clear()
        }

        action(ctx, state) {
            Ref3 {
                env: Environment {
                    sensor_island_in: Sensor::On,
                    ..state.env
                },
                ..state
            }
        }

    }

    concrete event SensorMainlandOutDepart {
        guard(ctx, state) {
            &&& state.env.sensor_mainland_out.is_on()
            &&& state.con.light_mainland.is_green()
        }

        action(ctx, state) {
            Ref3 {
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

    }

    concrete event SensorMainlandInDepart {
        guard(ctx, state) {
            state.env.sensor_mainland_in.is_on()
        }

        action(ctx, state) {
            Ref3 {
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

    }

    concrete event SensorIslandOutDepart {
        guard(ctx, state) {
            &&& state.env.sensor_island_out.is_on()
            &&& state.con.light_island.is_green()
        }

        action(ctx, state) {
            Ref3 {
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

    }

    concrete event SensorIslandInDepart {
        guard(ctx, state) {
            state.env.sensor_island_in.is_on()
        }

        action(ctx, state) {
            Ref3 {
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

}
use vstd::prelude::*;

use crate::ref2;

use crate::machine::*;
use crate::shared::*;

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

pub struct State {
    pub con: Controller,
    pub env: Environment,
}

impl Lift<ref2::State> for State {
    open spec fn lift(&self) -> ref2::State {
        ref2::State {
            cars_to_island: self.con.cars_to_island,
            cars_on_island: self.con.cars_on_island,
            cars_to_mainland: self.con.cars_to_mainland,

            light_mainland: self.con.light_mainland,
            light_island: self.con.light_island,

            car_left_mainland: self.con.car_left_mainland,
            car_left_island: self.con.car_left_island,
        }
    }
}

impl State {
    pub open spec fn validate(&self, ctx: BridgeCtx) -> bool {
        // Abstract
        &&& self.lift().validate(ctx)
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
}

impl Machine for State {
    type Ctx = BridgeCtx;

    open spec fn init(ctx: Self::Ctx) -> Self {
        State {
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
    }

    open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
        state.validate(ctx)
    }

    proof fn proof_init_safety(ctx: Self::Ctx) {}
}

impl Refinement for State {
    type Abstract = ref2::State;

    open spec fn lift_ctx(ctx: Self::Ctx) -> <Self::Abstract as Machine>::Ctx {
        ctx
    }

    proof fn proof_lift_ctx_valid(ctx: Self::Ctx) {}
    proof fn proof_init_lift(ctx: Self::Ctx) {}
    proof fn proof_lift_safe(ctx: Self::Ctx, state: Self) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.flag_entered_mainland.is_set()
        &&& state.con.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            con: Controller {
                flag_entered_mainland: Flag::Clear,
                cars_to_mainland: (state.con.cars_to_mainland - 1) as nat,
                ..state.con
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, ref2::MainlandIn> for MainlandIn {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.flag_left_mainland.is_set()
        &&& state.con.total_cars() + 1 <= ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, ref2::MainlandOut> for MainlandOut {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}

    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct IslandIn;
impl Event<State> for IslandIn {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.flag_entered_island.is_set()
        &&& state.con.cars_to_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            con: Controller {
                flag_entered_island: Flag::Clear,
                cars_to_island: (state.con.cars_to_island - 1) as nat,
                cars_on_island: state.con.cars_on_island + 1,
                ..state.con
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, ref2::IslandIn> for IslandIn {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct IslandOut;
impl Event<State> for IslandOut {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.flag_left_island.is_set()
        &&& state.con.cars_on_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

pub struct TurnGreenMainland;
impl Event<State> for TurnGreenMainland {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.light_mainland.is_red()
        &&& state.con.car_left_island
        &&& state.con.flag_left_island.is_clear()
        &&& state.con.cars_to_mainland == 0
        &&& state.con.total_cars() < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            con: Controller {
                light_mainland: TrafficLight::Green,
                light_island: TrafficLight::Red,
                car_left_mainland: false,
                ..state.con
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, ref2::TurnGreenMainland> for TurnGreenMainland {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct TurnGreenIsland;
impl Event<State> for TurnGreenIsland {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.con.light_island.is_red()
        &&& state.con.car_left_mainland
        &&& state.con.flag_left_mainland.is_clear()
        &&& state.con.cars_on_island > 0
        &&& state.con.cars_to_island == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            con: Controller {
                light_island: TrafficLight::Green,
                light_mainland: TrafficLight::Red,
                car_left_island: false,
                ..state.con
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, ref2::TurnGreenIsland> for TurnGreenIsland {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct SensorMainlandOutArrive;
impl Event<State> for SensorMainlandOutArrive {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_mainland_out.is_off()
        &&& state.con.flag_left_mainland.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            env: Environment {
                sensor_mainland_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorMainlandOutArrive {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_mainland_out.is_off() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorMainlandOutArrive {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorMainlandInArrive;
impl Event<State> for SensorMainlandInArrive {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_mainland_in.is_off()
        &&& state.con.flag_entered_mainland.is_clear()
        &&& state.env.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            env: Environment {
                sensor_mainland_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorMainlandInArrive {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_mainland_in.is_off() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorMainlandInArrive {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorIslandOutArrive;
impl Event<State> for SensorIslandOutArrive {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.cars_on_island > 0
        &&& state.env.sensor_island_out.is_off()
        &&& state.con.flag_left_island.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            env: Environment {
                sensor_island_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorIslandOutArrive {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_island_out.is_off() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorIslandOutArrive {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorIslandInArrive;
impl Event<State> for SensorIslandInArrive {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.cars_to_island > 0
        &&& state.env.sensor_island_in.is_off()
        &&& state.con.flag_entered_island.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            env: Environment {
                sensor_island_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorIslandInArrive {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_island_in.is_off() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorIslandInArrive {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorMainlandOutDepart;
impl Event<State> for SensorMainlandOutDepart {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_mainland_out.is_on()
        &&& state.con.light_mainland.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorMainlandOutDepart {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_mainland_out.is_on() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorMainlandOutDepart {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorMainlandInDepart;
impl Event<State> for SensorMainlandInDepart {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_mainland_in.is_on()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorMainlandInDepart {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_mainland_in.is_on() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

pub struct SensorIslandOutDepart;
impl Event<State> for SensorIslandOutDepart {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_island_out.is_on()
        &&& state.con.light_island.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorIslandOutDepart {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_island_out.is_on() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for SensorIslandOutDepart {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}

pub struct SensorIslandInDepart;
impl Event<State> for SensorIslandInDepart {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.env.sensor_island_in.is_on()
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
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

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for SensorIslandInDepart {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.env.sensor_island_in.is_on() as nat
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

proof fn proof_deadlock_free(ctx: BridgeCtx, state: State)
    requires
        ctx.valid(),
        State::inv(ctx, state),
    ensures {
        ||| MainlandIn::guard(ctx, state)
        ||| MainlandOut::guard(ctx, state)
        ||| IslandIn::guard(ctx, state)
        ||| IslandOut::guard(ctx, state)
        ||| TurnGreenMainland::guard(ctx, state)
        ||| TurnGreenIsland::guard(ctx, state)
        ||| SensorMainlandOutArrive::guard(ctx, state)
        ||| SensorMainlandOutDepart::guard(ctx, state)
        ||| SensorMainlandInArrive::guard(ctx, state)
        ||| SensorMainlandInDepart::guard(ctx, state)
        ||| SensorIslandOutArrive::guard(ctx, state)
        ||| SensorIslandOutDepart::guard(ctx, state)
        ||| SensorIslandInArrive::guard(ctx, state)
        ||| SensorIslandInDepart::guard(ctx, state)
    },
{}

}
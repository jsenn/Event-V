use vstd::prelude::*;

use crate::ref2;

use event_v::machine::*;
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

impl Lift<State, ref2::State> for State {
    open spec fn lift(state: State) -> ref2::State {
        ref2::State {
            cars_to_island: state.con.cars_to_island,
            cars_on_island: state.con.cars_on_island,
            cars_to_mainland: state.con.cars_to_mainland,

            light_mainland: state.con.light_mainland,
            light_island: state.con.light_island,

            car_left_mainland: state.con.car_left_mainland,
            car_left_island: state.con.car_left_island,
        }
    }
}

impl Lift<BridgeCtx, BridgeCtx> for State {
    open spec fn lift(ctx: BridgeCtx) -> BridgeCtx { ctx }
}

impl State {
    pub open spec fn lift(&self) -> ref2::State {
        <State as Lift<State, ref2::State>>::lift(*self)
    }

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
    type Context = BridgeCtx;

    open spec fn invariant(ctx: Self::Context, state: Self) -> bool {
        state.validate(ctx)
    }
}

pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(ctx: BridgeCtx, _input: ()) -> State {
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

    proof fn proof_safety(ctx: BridgeCtx, _input: ()) {}
}

impl Refinement for State {
    type Abstract = ref2::State;

    proof fn proof_lift_ctx_valid(ctx: BridgeCtx) {}
    proof fn proof_lift_safe(ctx: BridgeCtx, state: Self) {}
}

impl ConvergentRefinement for State {
    type Variant = (bool, bool, bool, bool, bool, bool, bool, bool);

    open spec fn variant(_ctx: Self::Context, state: Self) -> Self::Variant {
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
}

impl RefinedInit<State, ref2::Initialize> for Initialize {
    open spec fn lift_in(_input: ()) -> () { () }

    proof fn proof_simulation(ctx: BridgeCtx, _input: ()) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.flag_entered_mainland.is_set()
        &&& state.con.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            con: Controller {
                flag_entered_mainland: Flag::Clear,
                cars_to_mainland: (state.con.cars_to_mainland - 1) as nat,
                ..state.con
            },
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::MainlandIn> for MainlandIn {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.flag_left_mainland.is_set()
        &&& state.con.total_cars() + 1 <= ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::MainlandOut> for MainlandOut {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct IslandIn;
impl Event<State> for IslandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.flag_entered_island.is_set()
        &&& state.con.cars_to_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::IslandIn> for IslandIn {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct IslandOut;
impl Event<State> for IslandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.flag_left_island.is_set()
        &&& state.con.cars_on_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::IslandOut> for IslandOut {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct TurnGreenMainland;
impl Event<State> for TurnGreenMainland {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.light_mainland.is_red()
        &&& state.con.car_left_island
        &&& state.con.flag_left_island.is_clear()
        &&& state.con.cars_to_mainland == 0
        &&& state.con.total_cars() < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::TurnGreenMainland> for TurnGreenMainland {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct TurnGreenIsland;
impl Event<State> for TurnGreenIsland {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.con.light_island.is_red()
        &&& state.con.car_left_mainland
        &&& state.con.flag_left_mainland.is_clear()
        &&& state.con.cars_on_island > 0
        &&& state.con.cars_to_island == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref2::TurnGreenIsland> for TurnGreenIsland {
    open spec fn lift_in(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorMainlandOutArrive;
impl Event<State> for SensorMainlandOutArrive {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_mainland_out.is_off()
        &&& state.con.flag_left_mainland.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            env: Environment {
                sensor_mainland_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorMainlandOutArrive {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorMainlandInArrive;
impl Event<State> for SensorMainlandInArrive {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_mainland_in.is_off()
        &&& state.con.flag_entered_mainland.is_clear()
        &&& state.env.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            env: Environment {
                sensor_mainland_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorMainlandInArrive {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorIslandOutArrive;
impl Event<State> for SensorIslandOutArrive {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.cars_on_island > 0
        &&& state.env.sensor_island_out.is_off()
        &&& state.con.flag_left_island.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            env: Environment {
                sensor_island_out: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorIslandOutArrive {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorIslandInArrive;
impl Event<State> for SensorIslandInArrive {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.cars_to_island > 0
        &&& state.env.sensor_island_in.is_off()
        &&& state.con.flag_entered_island.is_clear()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            env: Environment {
                sensor_island_in: Sensor::On,
                ..state.env
            },
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorIslandInArrive {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorMainlandOutDepart;
impl Event<State> for SensorMainlandOutDepart {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_mainland_out.is_on()
        &&& state.con.light_mainland.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorMainlandOutDepart {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorMainlandInDepart;
impl Event<State> for SensorMainlandInDepart {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_mainland_in.is_on()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorMainlandInDepart {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorIslandOutDepart;
impl Event<State> for SensorIslandOutDepart {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_island_out.is_on()
        &&& state.con.light_island.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorIslandOutDepart {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct SensorIslandInDepart;
impl Event<State> for SensorIslandInDepart {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.env.sensor_island_in.is_on()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
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

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for SensorIslandInDepart {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

proof fn proof_deadlock_free(ctx: BridgeCtx, state: State)
    requires
        ctx.valid(),
        State::invariant(ctx, state),
    ensures {
        ||| MainlandIn::guard(ctx, state, ())
        ||| MainlandOut::guard(ctx, state, ())
        ||| IslandIn::guard(ctx, state, ())
        ||| IslandOut::guard(ctx, state, ())
        ||| TurnGreenMainland::guard(ctx, state, ())
        ||| TurnGreenIsland::guard(ctx, state, ())
        ||| SensorMainlandOutArrive::guard(ctx, state, ())
        ||| SensorMainlandOutDepart::guard(ctx, state, ())
        ||| SensorMainlandInArrive::guard(ctx, state, ())
        ||| SensorMainlandInDepart::guard(ctx, state, ())
        ||| SensorIslandOutArrive::guard(ctx, state, ())
        ||| SensorIslandOutDepart::guard(ctx, state, ())
        ||| SensorIslandInArrive::guard(ctx, state, ())
        ||| SensorIslandInDepart::guard(ctx, state, ())
    },
{}

}

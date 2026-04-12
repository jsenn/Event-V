use vstd::prelude::*;

use crate::ref1;

use verus_machine::machine::*;
use crate::shared::*;


verus! {

pub struct State {
    pub cars_to_island: nat,
    pub cars_on_island: nat,
    pub cars_to_mainland: nat,

    pub light_mainland: TrafficLight,
    pub light_island: TrafficLight,

    pub car_left_mainland: bool,
    pub car_left_island: bool,
}

impl Lift<ref1::State> for State {
    open spec fn lift(&self) -> ref1::State {
        ref1::State {
            cars_to_island: self.cars_to_island,
            cars_on_island: self.cars_on_island,
            cars_to_mainland: self.cars_to_mainland,
        }
    }
}

impl State {
    pub open spec fn validate(&self, ctx: BridgeCtx) -> bool {
        // Abstract
        &&& self.lift().validate(ctx)
        // Traffic lights
        &&& self.light_mainland.is_green() ==> {
            &&& self.cars_to_mainland == 0
            &&& self.lift().total_cars() < ctx.max_cars
        }
        &&& self.light_island.is_green() ==> self.cars_to_island == 0 && self.cars_on_island > 0
        &&& self.light_mainland.is_red() || self.light_island.is_red()
        // Car left flags
        &&& self.light_mainland.is_red() ==> self.car_left_mainland
        &&& self.light_island.is_red() ==> self.car_left_island
    }
}

impl Machine for State {
    type Ctx = BridgeCtx;

    open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
        state.validate(ctx)
    }
}

pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(ctx: BridgeCtx, _input: ()) -> State {
        State {
            cars_to_island: 0,
            cars_on_island: 0,
            cars_to_mainland: 0,

            light_mainland: TrafficLight::Green,
            light_island: TrafficLight::Red,

            car_left_mainland: false,
            car_left_island: true,
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, _input: ()) {}
}

impl Refinement for State {
    type Abstract = ref1::State;

    open spec fn lift_ctx(ctx: Self::Ctx) -> BridgeCtx {
        ctx
    }

    proof fn proof_lift_ctx_valid(ctx: Self::Ctx) {}
    proof fn proof_lift_safe(ctx: Self::Ctx, state: Self) {}
}

impl RefinedInit<State, ref1::Initialize> for Initialize {
    open spec fn lift_in(_input: ()) -> () { () }

    proof fn proof_simulation(ctx: BridgeCtx, _input: ()) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_to_mainland: (state.cars_to_mainland - 1) as nat,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::MainlandIn> for MainlandIn {
    open spec fn lift_in(_input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.light_mainland.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_to_island: state.cars_to_island + 1,
            light_mainland:
                if state.cars_to_island + state.cars_on_island + 1 == ctx.max_cars {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
            car_left_mainland: true,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::MainlandOut> for MainlandOut {
    open spec fn lift_in(_input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct IslandIn;
impl Event<State> for IslandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.cars_to_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_to_island: (state.cars_to_island - 1) as nat,
            cars_on_island: state.cars_on_island + 1,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::IslandIn> for IslandIn {
    open spec fn lift_in(_input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct IslandOut;
impl Event<State> for IslandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.light_island.is_green()
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_on_island: (state.cars_on_island - 1) as nat,
            cars_to_mainland: state.cars_to_mainland + 1,
            light_island:
                if state.cars_on_island == 1 {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
            car_left_island: true,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::IslandOut> for IslandOut {
    open spec fn lift_in(_input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct TurnGreenMainland;
impl Event<State> for TurnGreenMainland {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.light_mainland.is_red()
        &&& state.car_left_island
        &&& state.lift().total_cars() < ctx.max_cars
        &&& state.cars_to_mainland == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            light_mainland: TrafficLight::Green,
            light_island: TrafficLight::Red,
            car_left_mainland: false,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl ConvergentEvent<State> for TurnGreenMainland {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        (state.car_left_island as nat) + (state.car_left_mainland as nat)
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for TurnGreenMainland {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct TurnGreenIsland;
impl Event<State> for TurnGreenIsland {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.light_island.is_red()
        &&& state.car_left_mainland
        &&& state.cars_on_island > 0
        &&& state.cars_to_island == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            light_island: TrafficLight::Green,
            light_mainland: TrafficLight::Red,
            car_left_island: false,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl ConvergentEvent<State> for TurnGreenIsland {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        (state.car_left_island as nat) + (state.car_left_mainland as nat)
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for TurnGreenIsland {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}

proof fn proof_deadlock_free(ctx: BridgeCtx, state: State)
    requires
        ctx.valid(),
        State::inv(ctx, state),
    ensures {
        ||| MainlandIn::guard(ctx, state, ())
        ||| MainlandOut::guard(ctx, state, ())
        ||| IslandIn::guard(ctx, state, ())
        ||| IslandOut::guard(ctx, state, ())
        ||| TurnGreenMainland::guard(ctx, state, ())
        ||| TurnGreenIsland::guard(ctx, state, ())
    },
{}

}

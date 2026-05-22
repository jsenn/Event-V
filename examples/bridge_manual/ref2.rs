use vstd::prelude::*;

use crate::ref1;

use event_v::machine::*;
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

impl Lift<State, ref1::State> for State {
    open spec fn lift(state: State) -> ref1::State {
        ref1::State {
            cars_to_island: state.cars_to_island,
            cars_on_island: state.cars_on_island,
            cars_to_mainland: state.cars_to_mainland,
        }
    }
}

impl Lift<BridgeContext, BridgeContext> for State {
    open spec fn lift(context: BridgeContext) -> BridgeContext { context }
}

impl State {
    pub open spec fn lift(&self) -> ref1::State {
        <State as Lift<State, ref1::State>>::lift(*self)
    }

    pub open spec fn validate(&self, context: BridgeContext) -> bool {
        // Abstract
        &&& self.lift().validate(context)
        // Traffic lights
        &&& self.light_mainland.is_green() ==> {
            &&& self.cars_to_mainland == 0
            &&& self.lift().total_cars() < context.max_cars
        }
        &&& self.light_island.is_green() ==> self.cars_to_island == 0 && self.cars_on_island > 0
        &&& self.light_mainland.is_red() || self.light_island.is_red()
        // Car left flags
        &&& self.light_mainland.is_red() ==> self.car_left_mainland
        &&& self.light_island.is_red() ==> self.car_left_island
    }
}

impl Machine for State {
    type Context = BridgeContext;

    open spec fn invariant(context: Self::Context, state: Self) -> bool {
        state.validate(context)
    }
}

pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(context: BridgeContext, _input: ()) -> State {
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

    proof fn proof_safety(context: BridgeContext, _input: ()) {}
}

impl Refinement for State {
    type Abstract = ref1::State;

    proof fn proof_lift_context_valid(context: BridgeContext) {}
    proof fn proof_lift_safe(context: BridgeContext, state: Self) {}
}

impl ConvergentRefinement for State {
    type Variant = (bool, bool);

    open spec fn variant(_context: Self::Context, state: Self) -> Self::Variant {
        (state.car_left_island, state.car_left_mainland)
    }
}

impl RefinedInit<State, ref1::Initialize> for Initialize {
    open spec fn lift_in(_input: ()) -> () { () }

    proof fn proof_simulation(context: BridgeContext, _input: ()) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.cars_to_mainland > 0
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            cars_to_mainland: (state.cars_to_mainland - 1) as nat,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::MainlandIn> for MainlandIn {
    open spec fn lift_in(_context: BridgeContext, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_simulation(context: BridgeContext, state: State, _input: ()) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.light_mainland.is_green()
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            cars_to_island: state.cars_to_island + 1,
            light_mainland:
                if state.cars_to_island + state.cars_on_island + 1 == context.max_cars {
                    TrafficLight::Red
                } else {
                    TrafficLight::Green
                },
            car_left_mainland: true,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::MainlandOut> for MainlandOut {
    open spec fn lift_in(_context: BridgeContext, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_simulation(context: BridgeContext, state: State, _input: ()) {}
}

pub struct IslandIn;
impl Event<State> for IslandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.cars_to_island > 0
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            cars_to_island: (state.cars_to_island - 1) as nat,
            cars_on_island: state.cars_on_island + 1,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::IslandIn> for IslandIn {
    open spec fn lift_in(_context: BridgeContext, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_simulation(context: BridgeContext, state: State, _input: ()) {}
}

pub struct IslandOut;
impl Event<State> for IslandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.light_island.is_green()
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
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

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl RefinedEvent<State, ref1::IslandOut> for IslandOut {
    open spec fn lift_in(_context: BridgeContext, _state: State, _input: ()) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_simulation(context: BridgeContext, state: State, _input: ()) {}
}

pub struct TurnGreenMainland;
impl Event<State> for TurnGreenMainland {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        &&& state.light_mainland.is_red()
        &&& state.car_left_island
        &&& state.lift().total_cars() < context.max_cars
        &&& state.cars_to_mainland == 0
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            light_mainland: TrafficLight::Green,
            light_island: TrafficLight::Red,
            car_left_mainland: false,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl NewEvent<State> for TurnGreenMainland {
    proof fn proof_convergent(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_stuttering(context: BridgeContext, state: State, _input: ()) {}
}

pub struct TurnGreenIsland;
impl Event<State> for TurnGreenIsland {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        &&& state.light_island.is_red()
        &&& state.car_left_mainland
        &&& state.cars_on_island > 0
        &&& state.cars_to_island == 0
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            light_island: TrafficLight::Green,
            light_mainland: TrafficLight::Red,
            car_left_island: false,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

impl NewEvent<State> for TurnGreenIsland {
    proof fn proof_convergent(context: BridgeContext, state: State, _input: ()) {}
    proof fn proof_stuttering(context: BridgeContext, state: State, _input: ()) {}
}

proof fn proof_deadlock_free(context: BridgeContext, state: State)
    requires
        context.valid(),
        State::invariant(context, state),
    ensures {
        ||| MainlandIn::guard(context, state, ())
        ||| MainlandOut::guard(context, state, ())
        ||| IslandIn::guard(context, state, ())
        ||| IslandOut::guard(context, state, ())
        ||| TurnGreenMainland::guard(context, state, ())
        ||| TurnGreenIsland::guard(context, state, ())
    },
{}

}

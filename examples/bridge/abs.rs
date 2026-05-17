use vstd::prelude::*;

use event_v::machine::*;
use crate::shared::*;


verus! {

pub struct State {
    pub cars: nat,
}

impl State {
    pub open spec fn validate(&self, context: BridgeContext) -> bool {
        self.cars <= context.max_cars
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
            cars: 0,
        }
    }

    proof fn proof_safety(context: BridgeContext, _input: ()) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.cars > 0
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            cars: (state.cars - 1) as nat,
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(context: BridgeContext, state: State, _input: ()) -> bool {
        state.cars < context.max_cars
    }

    open spec fn action(context: BridgeContext, state: State, _input: ()) -> State {
        State {
            cars: (state.cars + 1),
            ..state
        }
    }

    open spec fn output(_context: BridgeContext, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: BridgeContext, state: State, _input: ()) {}
}

proof fn proof_deadlock_free(context: BridgeContext, state: State)
    requires
        context.valid(),
        State::invariant(context, state),
    ensures {
        ||| MainlandIn::guard(context, state, ())
        ||| MainlandOut::guard(context, state, ())
    },
{}

}

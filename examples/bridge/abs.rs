use vstd::prelude::*;

use verus_machine::machine::*;
use crate::shared::*;


verus! {

pub struct State {
    pub cars: nat,
}

impl State {
    pub open spec fn validate(&self, ctx: BridgeCtx) -> bool {
        self.cars <= ctx.max_cars
    }
}

impl Machine for State {
    type Context = BridgeCtx;

    open spec fn inv(ctx: Self::Context, state: Self) -> bool {
        state.validate(ctx)
    }
}

pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(ctx: BridgeCtx, _input: ()) -> State {
        State {
            cars: 0,
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, _input: ()) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.cars > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars: (state.cars - 1) as nat,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        state.cars < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars: (state.cars + 1),
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

proof fn proof_deadlock_free(ctx: BridgeCtx, state: State)
    requires
        ctx.valid(),
        State::inv(ctx, state),
    ensures {
        ||| MainlandIn::guard(ctx, state, ())
        ||| MainlandOut::guard(ctx, state, ())
    },
{}

}

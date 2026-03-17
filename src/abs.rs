use vstd::prelude::*;

use crate::machine::*;
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
    type Ctx = BridgeCtx;

    open spec fn init(ctx: Self::Ctx) -> Self {
        State {
            cars: 0,
        }
    }

    open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
        state.validate(ctx)
    }

    proof fn proof_init_safety(ctx: Self::Ctx) {}
}

pub struct MainlandIn;
impl Event<State> for MainlandIn {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        state.cars > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars: (state.cars - 1) as nat,
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        state.cars < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars: (state.cars + 1),
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

proof fn proof_deadlock_free(ctx: BridgeCtx, state: State)
    requires
        ctx.valid(),
        State::inv(ctx, state),
    ensures {
        ||| MainlandIn::guard(ctx, state)
        ||| MainlandOut::guard(ctx, state)
    },
{}

}
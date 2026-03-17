use vstd::prelude::*;

use crate::abs;

use crate::machine::*;
use crate::shared::*;


verus! {

pub struct State {
    pub cars_to_island: nat,
    pub cars_on_island: nat,
    pub cars_to_mainland: nat,
}

impl Lift<abs::State> for State {
    open spec fn lift(&self) -> abs::State {
        abs::State {
            cars: self.total_cars(),
        }
    }
}

impl State {
    pub open spec fn total_cars(&self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }

    pub open spec fn validate(&self, ctx: BridgeCtx) -> bool {
        &&& self.lift().validate(ctx)
        &&& self.cars_to_island == 0 || self.cars_to_mainland == 0
    }
}

impl Machine for State {
    type Ctx = BridgeCtx;
    
    open spec fn init(ctx: Self::Ctx) -> Self {
        State {
            cars_to_island: 0,
            cars_on_island: 0,
            cars_to_mainland: 0,
        }
    }
    
    open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
        state.validate(ctx)
    }
    
    proof fn proof_init_safety(ctx: Self::Ctx) {}
}

impl Refinement for State {
    type Abstract = abs::State;

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
        state.cars_to_mainland > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars_to_mainland: (state.cars_to_mainland - 1) as nat,
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, abs::MainlandIn> for MainlandIn {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct MainlandOut;
impl Event<State> for MainlandOut {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.cars_to_mainland == 0
        &&& state.total_cars() < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars_to_island: state.cars_to_island + 1,
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl RefinedEvent<State, abs::MainlandOut> for MainlandOut {
    proof fn proof_strengthening(ctx: BridgeCtx, state: State) {}
    proof fn proof_simulation(ctx: BridgeCtx, state: State) {}
}

pub struct IslandIn;
impl Event<State> for IslandIn {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        state.cars_to_island > 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars_to_island: (state.cars_to_island - 1) as nat,
            cars_on_island: state.cars_on_island + 1,
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for IslandIn {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.cars_to_island
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for IslandIn {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
}


pub struct IslandOut;
impl Event<State> for IslandOut {
    open spec fn guard(ctx: BridgeCtx, state: State) -> bool {
        &&& state.cars_on_island > 0
        &&& state.cars_to_island == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State) -> State {
        State {
            cars_on_island: (state.cars_on_island - 1) as nat,
            cars_to_mainland: state.cars_to_mainland + 1,
            ..state
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, state: State) {}
}

impl ConvergentEvent<State> for IslandOut {
    open spec fn variant(ctx: BridgeCtx, state: State) -> nat {
        state.cars_on_island
    }

    proof fn proof_convergence(ctx: BridgeCtx, state: State) {}
}

impl NewEvent<State> for IslandOut {
    proof fn proof_stuttering(ctx: BridgeCtx, state: State) {}
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
    },
{}

}
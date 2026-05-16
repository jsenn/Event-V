use vstd::prelude::*;

use crate::abs;

use event_v::machine::*;
use crate::shared::*;


verus! {

pub struct State {
    pub cars_to_island: nat,
    pub cars_on_island: nat,
    pub cars_to_mainland: nat,
}

impl Lift<State, abs::State> for State {
    open spec fn lift(state: State) -> abs::State {
        abs::State {
            cars: state.total_cars(),
        }
    }
}

impl Lift<BridgeCtx, BridgeCtx> for State {
    open spec fn lift(ctx: BridgeCtx) -> BridgeCtx { ctx }
}

impl State {
    pub open spec fn lift(&self) -> abs::State {
        <State as Lift<State, abs::State>>::lift(*self)
    }

    pub open spec fn total_cars(&self) -> nat {
        self.cars_to_island + self.cars_on_island + self.cars_to_mainland
    }

    pub open spec fn validate(&self, ctx: BridgeCtx) -> bool {
        &&& self.lift().validate(ctx)
        &&& self.cars_to_island == 0 || self.cars_to_mainland == 0
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
            cars_to_island: 0,
            cars_on_island: 0,
            cars_to_mainland: 0,
        }
    }

    proof fn proof_safety(ctx: BridgeCtx, _input: ()) {}
}

impl Refinement for State {
    type Abstract = abs::State;

    proof fn proof_lift_ctx_valid(ctx: BridgeCtx) {}
    proof fn proof_lift_safe(ctx: BridgeCtx, state: Self) {}
}

impl ConvergentRefinement for State {
    type Variant = (nat, nat);

    open spec fn variant(ctx: BridgeCtx, state: State) -> Self::Variant {
        (state.cars_to_island, state.cars_on_island)
    }
}

impl RefinedInit<State, abs::Initialize> for Initialize {
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

impl RefinedEvent<State, abs::MainlandIn> for MainlandIn {
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
        &&& state.cars_to_mainland == 0
        &&& state.total_cars() < ctx.max_cars
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_to_island: state.cars_to_island + 1,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl RefinedEvent<State, abs::MainlandOut> for MainlandOut {
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

impl NewEvent<State> for IslandIn {
    proof fn proof_convergent(ctx: BridgeCtx, state: State, _input: ()) {}
    proof fn proof_stuttering(ctx: BridgeCtx, state: State, _input: ()) {}
}


pub struct IslandOut;
impl Event<State> for IslandOut {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: BridgeCtx, state: State, _input: ()) -> bool {
        &&& state.cars_on_island > 0
        &&& state.cars_to_island == 0
    }

    open spec fn action(ctx: BridgeCtx, state: State, _input: ()) -> State {
        State {
            cars_on_island: (state.cars_on_island - 1) as nat,
            cars_to_mainland: state.cars_to_mainland + 1,
            ..state
        }
    }

    open spec fn output(_ctx: BridgeCtx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: BridgeCtx, state: State, _input: ()) {}
}

impl NewEvent<State> for IslandOut {
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
    },
{}

}

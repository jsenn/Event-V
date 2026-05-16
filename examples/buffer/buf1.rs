use vstd::prelude::*;

use crate::buf0;

use event_v::machine::*;

verus! {

/// Concrete buffer state: stores elements in a sequence.
pub struct State {
    pub data: Seq<nat>,
}

impl Lift<State, buf0::State> for State {
    open spec fn lift(state: State) -> buf0::State {
        buf0::State { size: state.data.len() }
    }
}

impl Lift<buf0::Ctx, buf0::Ctx> for State {
    open spec fn lift(ctx: buf0::Ctx) -> buf0::Ctx { ctx }
}

impl State {
    pub open spec fn lift(&self) -> buf0::State {
        <State as Lift<State, buf0::State>>::lift(*self)
    }

    pub open spec fn validate(&self, ctx: buf0::Ctx) -> bool {
        self.lift().validate(ctx)
    }
}

impl Machine for State {
    type Context = buf0::Ctx;

    open spec fn inv(ctx: Self::Context, state: Self) -> bool {
        state.validate(ctx)
    }
}

impl Refinement for State {
    type Abstract = buf0::State;

    proof fn proof_lift_ctx_valid(ctx: buf0::Ctx) {}
    proof fn proof_lift_safe(ctx: buf0::Ctx, state: Self) {}
}

/// Initialization: empty buffer.
pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(_ctx: buf0::Ctx, _input: ()) -> State {
        State { data: Seq::empty() }
    }

    proof fn proof_safety(_ctx: buf0::Ctx, _input: ()) {}
}

impl RefinedInit<State, buf0::Initialize> for Initialize {
    open spec fn lift_in(_input: ()) -> () { () }

    proof fn proof_simulation(_ctx: buf0::Ctx, _input: ()) {}
}

/// Put: prepend an element to the buffer.
/// Input = nat (the element to add). Refines buf0::Put.
pub struct Put;
impl Event<State> for Put {
    type Input = nat;
    type Output = ();

    open spec fn guard(ctx: buf0::Ctx, state: State, _input: nat) -> bool {
        state.data.len() < ctx.max_size
    }

    open spec fn action(_ctx: buf0::Ctx, state: State, input: nat) -> State {
        State { data: seq![input].add(state.data) }
    }

    open spec fn output(_ctx: buf0::Ctx, _state: State, _input: nat) -> () { () }

    proof fn proof_safety(ctx: buf0::Ctx, state: State, input: nat) {}
}

impl RefinedEvent<State, buf0::Put> for Put {
    /// Discard the element — the abstract level doesn't track it.
    open spec fn lift_in(_ctx: buf0::Ctx, _state: State, _input: nat) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: buf0::Ctx, state: State, _input: nat) {}
    proof fn proof_simulation(ctx: buf0::Ctx, state: State, input: nat) {}
}

/// PutLast: append an element to the end. Also refines buf0::Put.
/// Demonstrates multiple concrete events refining the same abstract event.
pub struct PutLast;
impl Event<State> for PutLast {
    type Input = nat;
    type Output = ();

    open spec fn guard(ctx: buf0::Ctx, state: State, _input: nat) -> bool {
        state.data.len() < ctx.max_size
    }

    open spec fn action(_ctx: buf0::Ctx, state: State, input: nat) -> State {
        State { data: state.data.push(input) }
    }

    open spec fn output(_ctx: buf0::Ctx, _state: State, _input: nat) -> () { () }

    proof fn proof_safety(ctx: buf0::Ctx, state: State, input: nat) {}
}

impl RefinedEvent<State, buf0::Put> for PutLast {
    open spec fn lift_in(_ctx: buf0::Ctx, _state: State, _input: nat) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(ctx: buf0::Ctx, state: State, _input: nat) {}
    proof fn proof_simulation(ctx: buf0::Ctx, state: State, input: nat) {}
}

/// Fetch: remove the first element from the buffer.
/// Output = nat (the removed element). Refines buf0::Fetch.
pub struct Fetch;
impl Event<State> for Fetch {
    type Input = ();
    type Output = nat;

    open spec fn guard(_ctx: buf0::Ctx, state: State, _input: ()) -> bool {
        state.data.len() > 0
    }

    open spec fn action(_ctx: buf0::Ctx, state: State, _input: ()) -> State {
        State { data: state.data.subrange(1, state.data.len() as int) }
    }

    open spec fn output(_ctx: buf0::Ctx, state: State, _input: ()) -> nat {
        state.data[0]
    }

    proof fn proof_safety(ctx: buf0::Ctx, state: State, _input: ()) {}
}

impl RefinedEvent<State, buf0::Fetch> for Fetch {
    open spec fn lift_in(_ctx: buf0::Ctx, _state: State, _input: ()) -> () { () }
    /// Discard the fetched element — the abstract level doesn't return one.
    open spec fn lift_out(_output: nat) -> () { () }

    proof fn proof_strengthening(_ctx: buf0::Ctx, state: State, _input: ()) {}
    proof fn proof_simulation(ctx: buf0::Ctx, state: State, _input: ()) {}
}

/// GetSize: query the buffer length. Refines buf0::GetSize.
pub struct GetSize;
impl Event<State> for GetSize {
    type Input = ();
    type Output = nat;

    open spec fn guard(_ctx: buf0::Ctx, _state: State, _input: ()) -> bool {
        true
    }

    open spec fn action(_ctx: buf0::Ctx, state: State, _input: ()) -> State {
        state
    }

    open spec fn output(_ctx: buf0::Ctx, state: State, _input: ()) -> nat {
        state.data.len()
    }

    proof fn proof_safety(_ctx: buf0::Ctx, _state: State, _input: ()) {}
}

impl RefinedEvent<State, buf0::GetSize> for GetSize {
    open spec fn lift_in(_ctx: buf0::Ctx, _state: State, _input: ()) -> () { () }
    /// Output matches exactly — both return the size.
    open spec fn lift_out(output: nat) -> nat { output }

    proof fn proof_strengthening(_ctx: buf0::Ctx, _state: State, _input: ()) {}
    proof fn proof_simulation(_ctx: buf0::Ctx, state: State, _input: ()) {}
}

}

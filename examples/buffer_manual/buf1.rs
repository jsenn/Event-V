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

impl Lift<buf0::Context, buf0::Context> for State {
    open spec fn lift(context: buf0::Context) -> buf0::Context { context }
}

impl State {
    pub open spec fn lift(&self) -> buf0::State {
        <State as Lift<State, buf0::State>>::lift(*self)
    }

    pub open spec fn validate(&self, context: buf0::Context) -> bool {
        self.lift().validate(context)
    }
}

impl Machine for State {
    type Context = buf0::Context;

    open spec fn invariant(context: Self::Context, state: Self) -> bool {
        state.validate(context)
    }
}

impl Refinement for State {
    type Abstract = buf0::State;

    proof fn proof_lift_context_valid(context: buf0::Context) {}
    proof fn proof_lift_safe(context: buf0::Context, state: Self) {}
}

/// Initialization: empty buffer.
pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(_context: buf0::Context, _input: ()) -> State {
        State { data: Seq::empty() }
    }

    proof fn proof_safety(_context: buf0::Context, _input: ()) {}
}

impl RefinedInit<State, buf0::Initialize> for Initialize {
    open spec fn lift_in(_input: ()) -> () { () }

    proof fn proof_simulation(_context: buf0::Context, _input: ()) {}
}

/// Put: prepend an element to the buffer.
/// Input = nat (the element to add). Refines buf0::Put.
pub struct Put;
impl Event<State> for Put {
    type Input = nat;
    type Output = ();

    open spec fn guard(context: buf0::Context, state: State, _input: nat) -> bool {
        state.data.len() < context.max_size
    }

    open spec fn action(_context: buf0::Context, state: State, input: nat) -> State {
        State { data: seq![input].add(state.data) }
    }

    open spec fn output(_context: buf0::Context, _state: State, _input: nat) -> () { () }

    proof fn proof_safety(context: buf0::Context, state: State, input: nat) {}
}

impl RefinedEvent<State, buf0::Put> for Put {
    /// Discard the element — the abstract level doesn't track it.
    open spec fn lift_in(_context: buf0::Context, _state: State, _input: nat) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: buf0::Context, state: State, _input: nat) {}
    proof fn proof_simulation(context: buf0::Context, state: State, input: nat) {}
}

/// PutLast: append an element to the end. Also refines buf0::Put.
/// Demonstrates multiple concrete events refining the same abstract event.
pub struct PutLast;
impl Event<State> for PutLast {
    type Input = nat;
    type Output = ();

    open spec fn guard(context: buf0::Context, state: State, _input: nat) -> bool {
        state.data.len() < context.max_size
    }

    open spec fn action(_context: buf0::Context, state: State, input: nat) -> State {
        State { data: state.data.push(input) }
    }

    open spec fn output(_context: buf0::Context, _state: State, _input: nat) -> () { () }

    proof fn proof_safety(context: buf0::Context, state: State, input: nat) {}
}

impl RefinedEvent<State, buf0::Put> for PutLast {
    open spec fn lift_in(_context: buf0::Context, _state: State, _input: nat) -> () { () }
    open spec fn lift_out(_output: ()) -> () { () }

    proof fn proof_strengthening(context: buf0::Context, state: State, _input: nat) {}
    proof fn proof_simulation(context: buf0::Context, state: State, input: nat) {}
}

/// Fetch: remove the first element from the buffer.
/// Output = nat (the removed element). Refines buf0::Fetch.
pub struct Fetch;
impl Event<State> for Fetch {
    type Input = ();
    type Output = nat;

    open spec fn guard(_context: buf0::Context, state: State, _input: ()) -> bool {
        state.data.len() > 0
    }

    open spec fn action(_context: buf0::Context, state: State, _input: ()) -> State {
        State { data: state.data.subrange(1, state.data.len() as int) }
    }

    open spec fn output(_context: buf0::Context, state: State, _input: ()) -> nat {
        state.data[0]
    }

    proof fn proof_safety(context: buf0::Context, state: State, _input: ()) {}
}

impl RefinedEvent<State, buf0::Fetch> for Fetch {
    open spec fn lift_in(_context: buf0::Context, _state: State, _input: ()) -> () { () }
    /// Discard the fetched element — the abstract level doesn't return one.
    open spec fn lift_out(_output: nat) -> () { () }

    proof fn proof_strengthening(_context: buf0::Context, state: State, _input: ()) {}
    proof fn proof_simulation(context: buf0::Context, state: State, _input: ()) {}
}

/// GetSize: query the buffer length. Refines buf0::GetSize.
pub struct GetSize;
impl Event<State> for GetSize {
    type Input = ();
    type Output = nat;

    open spec fn guard(_context: buf0::Context, _state: State, _input: ()) -> bool {
        true
    }

    open spec fn action(_context: buf0::Context, state: State, _input: ()) -> State {
        state
    }

    open spec fn output(_context: buf0::Context, state: State, _input: ()) -> nat {
        state.data.len()
    }

    proof fn proof_safety(_context: buf0::Context, _state: State, _input: ()) {}
}

impl RefinedEvent<State, buf0::GetSize> for GetSize {
    open spec fn lift_in(_context: buf0::Context, _state: State, _input: ()) -> () { () }
    /// Output matches exactly — both return the size.
    open spec fn lift_out(output: nat) -> nat { output }

    proof fn proof_strengthening(_context: buf0::Context, _state: State, _input: ()) {}
    proof fn proof_simulation(_context: buf0::Context, state: State, _input: ()) {}
}

}

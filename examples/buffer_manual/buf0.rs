use vstd::prelude::*;

use event_v::machine::*;

verus! {

/// Shared context for all buffer machines.
pub struct Context {
    pub max_size: nat,
}

impl MachineContext for Context {
    open spec fn valid(&self) -> bool {
        self.max_size > 0
    }
}

/// Abstract buffer state: only tracks the number of elements.
pub struct State {
    pub size: nat,
}

impl State {
    pub open spec fn validate(&self, context: Context) -> bool {
        self.size <= context.max_size
    }
}

impl Machine for State {
    type Context = Context;

    open spec fn invariant(context: Self::Context, state: Self) -> bool {
        state.validate(context)
    }
}

/// Initialization: empty buffer.
pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(_context: Context, _input: ()) -> State {
        State { size: 0 }
    }

    proof fn proof_safety(_context: Context, _input: ()) {}
}

/// Put: add an element (abstract: just increment size).
pub struct Put;
impl Event<State> for Put {
    type Input = ();
    type Output = ();

    open spec fn guard(context: Context, state: State, _input: ()) -> bool {
        state.size < context.max_size
    }

    open spec fn action(_context: Context, state: State, _input: ()) -> State {
        State { size: state.size + 1 }
    }

    open spec fn output(_context: Context, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: Context, state: State, _input: ()) {}
}

/// Fetch: remove an element (abstract: just decrement size).
pub struct Fetch;
impl Event<State> for Fetch {
    type Input = ();
    type Output = ();

    open spec fn guard(_context: Context, state: State, _input: ()) -> bool {
        state.size > 0
    }

    open spec fn action(_context: Context, state: State, _input: ()) -> State {
        State { size: (state.size - 1) as nat }
    }

    open spec fn output(_context: Context, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(context: Context, state: State, _input: ()) {}
}

/// GetSize: query the current size (no state change, output = size).
pub struct GetSize;
impl Event<State> for GetSize {
    type Input = ();
    type Output = nat;

    open spec fn guard(_context: Context, _state: State, _input: ()) -> bool {
        true
    }

    open spec fn action(_context: Context, state: State, _input: ()) -> State {
        state
    }

    open spec fn output(_context: Context, state: State, _input: ()) -> nat {
        state.size
    }

    proof fn proof_safety(_context: Context, _state: State, _input: ()) {}
}

proof fn proof_deadlock_free(context: Context, state: State)
    requires
        context.valid(),
        State::invariant(context, state),
    ensures
        Put::guard(context, state, ()) || Fetch::guard(context, state, ()) || GetSize::guard(context, state, ()),
{}

}

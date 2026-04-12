use vstd::prelude::*;

use verus_machine::machine::*;

verus! {

/// Shared context for all buffer machines.
pub struct Ctx {
    pub max_size: nat,
}

impl MachineContext for Ctx {
    open spec fn valid(&self) -> bool {
        self.max_size > 0
    }
}

/// Abstract buffer state: only tracks the number of elements.
pub struct State {
    pub size: nat,
}

impl State {
    pub open spec fn validate(&self, ctx: Ctx) -> bool {
        self.size <= ctx.max_size
    }
}

impl Machine for State {
    type Ctx = Ctx;

    open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
        state.validate(ctx)
    }
}

/// Initialization: empty buffer.
pub struct Initialize;
impl Init<State> for Initialize {
    type Input = ();

    open spec fn init(_ctx: Ctx, _input: ()) -> State {
        State { size: 0 }
    }

    proof fn proof_safety(_ctx: Ctx, _input: ()) {}
}

/// Put: add an element (abstract: just increment size).
pub struct Put;
impl Event<State> for Put {
    type Input = ();
    type Output = ();

    open spec fn guard(ctx: Ctx, state: State, _input: ()) -> bool {
        state.size < ctx.max_size
    }

    open spec fn action(_ctx: Ctx, state: State, _input: ()) -> State {
        State { size: state.size + 1 }
    }

    open spec fn output(_ctx: Ctx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: Ctx, state: State, _input: ()) {}
}

/// Fetch: remove an element (abstract: just decrement size).
pub struct Fetch;
impl Event<State> for Fetch {
    type Input = ();
    type Output = ();

    open spec fn guard(_ctx: Ctx, state: State, _input: ()) -> bool {
        state.size > 0
    }

    open spec fn action(_ctx: Ctx, state: State, _input: ()) -> State {
        State { size: (state.size - 1) as nat }
    }

    open spec fn output(_ctx: Ctx, _state: State, _input: ()) -> () { () }

    proof fn proof_safety(ctx: Ctx, state: State, _input: ()) {}
}

/// GetSize: query the current size (no state change, output = size).
pub struct GetSize;
impl Event<State> for GetSize {
    type Input = ();
    type Output = nat;

    open spec fn guard(_ctx: Ctx, _state: State, _input: ()) -> bool {
        true
    }

    open spec fn action(_ctx: Ctx, state: State, _input: ()) -> State {
        state
    }

    open spec fn output(_ctx: Ctx, state: State, _input: ()) -> nat {
        state.size
    }

    proof fn proof_safety(_ctx: Ctx, _state: State, _input: ()) {}
}

proof fn proof_deadlock_free(ctx: Ctx, state: State)
    requires
        ctx.valid(),
        State::inv(ctx, state),
    ensures
        Put::guard(ctx, state, ()) || Fetch::guard(ctx, state, ()) || GetSize::guard(ctx, state, ()),
{}

}

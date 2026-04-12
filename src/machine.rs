use vstd::prelude::*;

verus! {

pub trait MachineContext: Sized {
    spec fn valid(&self) -> bool;
}

pub trait Lift<Abstract>: Sized {
    spec fn lift(&self) -> Abstract;
}

pub trait Machine: Sized {
    type Ctx: MachineContext;

    spec fn inv(ctx: Self::Ctx, state: Self) -> bool;
}

pub trait Init<M: Machine> {
    type Input;

    spec fn init(ctx: M::Ctx, input: Self::Input) -> M;

    proof fn proof_safety(ctx: M::Ctx, input: Self::Input)
        requires ctx.valid(),
        ensures M::inv(ctx, Self::init(ctx, input));
}

pub trait Event<M: Machine> {
    type Input;
    type Output;

    spec fn guard(ctx: M::Ctx, state: M, input: Self::Input) -> bool;

    spec fn action(ctx: M::Ctx, state: M, input: Self::Input) -> M;

    spec fn output(ctx: M::Ctx, state: M, input: Self::Input) -> Self::Output;

    proof fn proof_safety(ctx: M::Ctx, state: M, input: Self::Input)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state, input),
        ensures
            M::inv(ctx, Self::action(ctx, state, input));
}

// ---------------------------------------------------------------------------
// Refinement
// ---------------------------------------------------------------------------

pub trait Refinement: Machine + Lift<Self::Abstract>
{
    type Abstract: Machine;

    spec fn lift_ctx(ctx: Self::Ctx) -> <Self::Abstract as Machine>::Ctx;

    proof fn proof_lift_ctx_valid(ctx: Self::Ctx)
        requires
            ctx.valid(),
        ensures
            Self::lift_ctx(ctx).valid();

    proof fn proof_lift_safe(ctx: Self::Ctx, state: Self)
        requires
            ctx.valid(),
            Self::inv(ctx, state),
        ensures
            Self::Abstract::inv(Self::lift_ctx(ctx), state.lift());
}

pub trait RefinedInit<M: Refinement, Abstract: Init<M::Abstract>>: Init<M> {
    spec fn lift_in(input: <Self as Init<M>>::Input) -> <Abstract as Init<M::Abstract>>::Input;

    proof fn proof_simulation(ctx: M::Ctx, input: <Self as Init<M>>::Input)
        requires
            ctx.valid(),
        ensures
            Self::init(ctx, input).lift() == Abstract::init(M::lift_ctx(ctx), Self::lift_in(input));
}

pub trait RefinedEvent<M: Refinement, Abstract: Event<M::Abstract>>: Event<M> {
    spec fn lift_in(input: <Self as Event<M>>::Input) -> <Abstract as Event<M::Abstract>>::Input;

    spec fn lift_out(output: <Self as Event<M>>::Output) -> <Abstract as Event<M::Abstract>>::Output;

    proof fn proof_strengthening(ctx: M::Ctx, state: M, input: <Self as Event<M>>::Input)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state, input),
        ensures
            Abstract::guard(M::lift_ctx(ctx), state.lift(), Self::lift_in(input));

    proof fn proof_simulation(ctx: M::Ctx, state: M, input: <Self as Event<M>>::Input)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state, input),
            Abstract::guard(M::lift_ctx(ctx), state.lift(), Self::lift_in(input)),
        ensures
            Self::action(ctx, state, input).lift() == Abstract::action(M::lift_ctx(ctx), state.lift(), Self::lift_in(input)),
            Self::lift_out(Self::output(ctx, state, input)) == Abstract::output(M::lift_ctx(ctx), state.lift(), Self::lift_in(input));
}

// ---------------------------------------------------------------------------
// Convergence (new/concrete events)
// ---------------------------------------------------------------------------

pub trait ConvergentEvent<M: Machine>: Event<M> {
    spec fn variant(ctx: M::Ctx, state: M) -> nat;

    proof fn proof_convergence(ctx: M::Ctx, state: M, input: <Self as Event<M>>::Input)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state, input),
        ensures
            Self::variant(ctx, Self::action(ctx, state, input)) < Self::variant(ctx, state);
}

pub trait NewEvent<M: Refinement>: ConvergentEvent<M> {
    proof fn proof_stuttering(ctx: M::Ctx, state: M, input: <Self as Event<M>>::Input)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state, input),
        ensures
            Self::action(ctx, state, input).lift() == state.lift();
}

}

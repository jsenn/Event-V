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

    spec fn init(ctx: Self::Ctx) -> Self;

    spec fn inv(ctx: Self::Ctx, state: Self) -> bool;

    proof fn proof_init_safety(ctx: Self::Ctx)
        requires ctx.valid(),
        ensures Self::inv(ctx, Self::init(ctx));
}

pub trait Event<M: Machine> {
    spec fn guard(ctx: M::Ctx, state: M) -> bool;

    spec fn action(ctx: M::Ctx, state: M) -> M;
    
    proof fn proof_safety(ctx: M::Ctx, state: M)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state),
        ensures
            M::inv(ctx, Self::action(ctx, state));
}

pub trait Refinement: Machine + Lift<Self::Abstract>
{
    type Abstract: Machine;

    spec fn lift_ctx(ctx: Self::Ctx) -> <Self::Abstract as Machine>::Ctx;

    proof fn proof_lift_ctx_valid(ctx: Self::Ctx)
        requires
            ctx.valid(),
        ensures
            Self::lift_ctx(ctx).valid();
    
    proof fn proof_init_lift(ctx: Self::Ctx)
        requires
            ctx.valid(),
        ensures
            Self::init(ctx).lift() == Self::Abstract::init(Self::lift_ctx(ctx));

    proof fn proof_lift_safe(ctx: Self::Ctx, state: Self)
        requires
            ctx.valid(),
            Self::inv(ctx, state),
        ensures
            Self::Abstract::inv(Self::lift_ctx(ctx), state.lift());
}

pub trait RefinedEvent<M: Refinement, Abstract: Event<M::Abstract>>: Event<M> {
    proof fn proof_strengthening(ctx: M::Ctx, state: M)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state),
        ensures
            Abstract::guard(M::lift_ctx(ctx), state.lift());
    
    proof fn proof_simulation(ctx: M::Ctx, state: M)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state),
            Abstract::guard(M::lift_ctx(ctx), state.lift()),
        ensures
            Self::action(ctx, state).lift() == Abstract::action(M::lift_ctx(ctx), state.lift());
}

pub trait ConvergentEvent<M: Machine>: Event<M> {
    spec fn variant(ctx: M::Ctx, state: M) -> nat;

    proof fn proof_convergence(ctx: M::Ctx, state: M)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state),
        ensures
            Self::variant(ctx, Self::action(ctx, state)) < Self::variant(ctx, state);
}

pub trait NewEvent<M: Refinement>: ConvergentEvent<M> {
    proof fn proof_stuttering(ctx: M::Ctx, state: M)
        requires
            ctx.valid(),
            M::inv(ctx, state),
            Self::guard(ctx, state),
        ensures
            Self::action(ctx, state).lift() == state.lift();
}

}
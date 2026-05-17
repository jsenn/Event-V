//! # Machine
//! 
//! The `machine` module contains the core trait machinery that defines state machines, events,
//! refinement, and bisimulation.

use vstd::prelude::*;

use crate::lex_lt::LexLt;

verus! {

/// Defines the requirements of a machine's `Context` type. The context contains all the
/// information needed to construct a machine. The context is available to all events of a machine,
/// but it is immutable.
/// 
/// For example, a `BufferMachine` might have a `max_size` in its context, while a `VendingMachine`
/// might have an initial inventory and amount of change.
///
/// # Examples
/// ```rust,ignore
/// pub struct CounterContext {
///     pub max_value: nat,
/// }
///
/// impl MachineContext for CounterContext {
///    open spec fn valid(&self) -> bool {
///        self.max_value > 0
///    }
/// }
/// ```
pub trait MachineContext: Sized {
    /// A predicate that checks if a given context is valid.
    spec fn valid(&self) -> bool;
}

/// A `Machine` is the fundamental concept in `event_v`. It represents a piece of state that
/// is constructed from a `MachineContext`, and which may be evolved by various `Events`.
///
/// # Examples
/// ```rust,ignore
/// pub struct CounterContext {
///     pub max_value: nat,
/// }
///
/// impl MachineContext for CounterContext {
///    open spec fn valid(&self) -> bool {
///        self.max_value > 0
///    }
/// }
///
/// pub struct Counter {
///     pub value: nat,
/// }
///
/// impl Machine for Counter {
///     type Context = Context;
///
///     open spec fn invariant(context: Self::Context, state: Self) -> bool {
///         self.value <= context.max_value
///     }
/// }
/// ```
pub trait Machine: Sized {
    /// The type of the context object for this machine
    type Context: MachineContext;

    /// The machine's **invariant** defines what it means for the machine to be in a valid state.
    spec fn invariant(context: Self::Context, state: Self) -> bool;
}

/// **Lift** a concrete representation (machine context or state) to an abstract one.
pub trait Lift<Concrete, Abstract> {
    /// Map a concrete value to its abstract representation.
    spec fn lift(concrete: Concrete) -> Abstract;
}

/// The `Init` trait represents a special event that runs once at the beginning of a machine's
/// lifetime. A machine can have multiple `Init`s, but only one can be used in a given trajectory.
/// 
/// # Examples
/// ```rust,ignore
/// pub struct CounterContext {
///     pub max_value: nat,
/// }
///
/// impl MachineContext for CounterContext {
///    open spec fn valid(&self) -> bool {
///        self.max_value > 0
///    }
/// }
///
/// pub struct Counter {
///     pub value: nat,
/// }
///
/// impl Machine for Counter {
///     type Context = CounterContext;
///
///     open spec fn invariant(context: Self::Context, state: Self) -> bool {
///         self.value <= context.max_value
///     }
/// }
/// 
/// pub struct InitializeToZero;
/// impl Init<Counter> for InitializeToZero {
///     type Input = ();
///
///     open spec fn init(_context: CounterContext, _input: ()) -> Counter {
///         Counter { value: 0 }
///     }
///
///     proof fn proof_safety(_context: CounterContext, _input: ()) {}
/// }
///
/// // The second initialization takes an initial value.
/// pub struct InitializeToValue;
/// impl Init<Counter> for InitializeToValue {
///     type Input = nat;
///
///     open spec fn init(_context: CounterContext, input: nat) -> Counter {
///         Counter { value: input }
///     }
///
///     proof fn proof_safety(_context: CounterContext, input: nat) {}
/// }
/// ```
pub trait Init<M: Machine> {
    /// The init event's input type
    type Input;

    /// Produce a `Machine` instance given a context and an input.
    spec fn init(context: M::Context, input: Self::Input) -> M;

    /// Prove that given a valid context and input, the machine is well-formed after
    /// initialization.
    proof fn proof_safety(context: M::Context, input: Self::Input)
        requires context.valid(),
        ensures M::invariant(context, Self::init(context, input));
}

/// Represents an event that modifies a machine's state. An event has 3 basic components:
/// * A **guard** predicate, which says when the event can fire;
/// * An **action**, which defines how the event changes the machine's state; and
/// * An **output** function, which produces an output after the event's action.
/// 
/// In order for an event to be valid, it has to guarantee that it will never produce an invalid
/// state from a valid one. This guarantee is provided by the event's **safety proof**.
///
/// # Examples
/// ```rust,ignore
/// pub struct CounterContext {
///     pub max_value: nat,
/// }
///
/// impl MachineContext for CounterContext {
///    open spec fn valid(&self) -> bool {
///        self.max_value > 0
///    }
/// }
///
/// pub struct Counter {
///     pub value: nat,
/// }
///
/// impl Machine for Counter {
///     type Context = Context;
///
///     open spec fn invariant(context: Self::Context, state: Self) -> bool {
///         self.value <= context.max_value
///     }
/// }
/// 
/// pub struct InitializeToZero;
/// impl Init<Counter> for InitializeToZero {
///     type Input = ();
///
///     open spec fn init(_context: CounterContext, _input: ()) -> Counter {
///         Counter { value: 0 }
///     }
///
///     proof fn proof_safety(_context: CounterContext, _input: ()) {}
/// }
///
/// /// The `AddValue` event adds a given value to the Counter, returning the counter's old value.
/// pub struct AddValue;
/// impl Event<Counter> for AddValue {
///     type Input = nat;
///     type Output = nat;
///
///     open spec fn guard(context: CounterContext, state: Counter, input: nat) -> bool {
///         state.value + input <= context.max_value
///     }
///
///     open spec fn action(_context: CounterContext, state: Counter, input: nat) -> State {
///         State { value: state.size + input }
///     }
///
///     open spec fn output(_context: CounterContext, state: Counter, _input: nat) -> nat {
///         state.value
///     }
///
///     proof fn proof_safety(context: CounterContext, state: Counter, _input: nat) {}
/// }
pub trait Event<M: Machine> {
    /// The type this event takes as input
    type Input;

    /// The type this event produces as output
    type Output;

    /// Determine whether this event is allowed to fire in a given state and for a given input.
    spec fn guard(context: M::Context, state: M, input: Self::Input) -> bool;

    /// Specify how this event transforms the current state into the next state given an input.
    spec fn action(context: M::Context, state: M, input: Self::Input) -> M;

    /// Produce an output given the current state and the event's input.
    spec fn output(context: M::Context, state: M, input: Self::Input) -> Self::Output;

    /// Prove that this event can never transform a valid state into an invalid one, so long as the
    /// event's guard is satisfied.
    proof fn proof_safety(context: M::Context, state: M, input: Self::Input)
        requires
            context.valid(),
            M::invariant(context, state),
            Self::guard(context, state, input),
        ensures
            M::invariant(context, Self::action(context, state, input));
}

/// A `Refinement` maps a `Machine` to a second more abstract `Machine` to which it adds some
/// detail or sophistication. Refinement allows us to progressively add detail to a state machine,
/// stating simple properties at an abstract level at which they are easier to prove, and adding
/// detail incrementally. This is a powerful way of creating complex state machines without getting
/// lost in the weeds.
/// 
/// A `Refinement` must provide a way to map the concrete machine's context and state into those of
/// the abstract machine. It must also prove that these mappings are valid. Specifically, it must
/// prove:
/// 1. That the `lift_context` function maps a valid concrete context onto a valid abstract one; and
/// 2. That `lift`ing a valid concrete state into an abstract state preserves the abstract
///    machine's invariant.
/// 
/// A concrete machine may also include new events that do not have an abstract counterpart. This
/// is only safe if the refinement can prove that the abstract machine will eventually be allowed
/// to make progress--otherwise a concrete machine could deadlock its abstract equivalent. To do
/// this, the refinement must provide a **Variant** type and a function variant(). Variant must be
/// **well-founded**. That is, there must be a finite number of instances of Variant less than any
/// given instance.
/// 
/// Then, each [`NewEvent`] provides a proof that it decreases the global variant. Due to the well-
/// foundedness property, the variant acts as a finite amount of "fuel" that the concrete machine
/// can run on before an abstract event must take place, preventing deadlock.
pub trait Refinement: Machine
    + Lift<Self, Self::Abstract>
    + Lift<Self::Context, <Self::Abstract as Machine>::Context>
{
    /// The abstract machine being refined.
    type Abstract: Machine;

    /// Prove that lifting a valid concrete context produces a valid abstract one.
    proof fn proof_lift_context_valid(context: Self::Context)
        requires
            context.valid(),
        ensures
            Self::lift(context).valid();

    /// Prove that lifting a valid concrete state produces a valid abstract state.
    proof fn proof_lift_safe(context: Self::Context, state: Self)
        requires
            context.valid(),
            Self::invariant(context, state),
        ensures
            <Self::Abstract as Machine>::invariant(Self::lift(context), Self::lift(state));
}

/// A refinement that supplies a well-founded variant so that concrete events (those without an
/// abstract counterpart) can be proven to converge. Implement this in addition to [`Refinement`]
/// whenever the refinement introduces [`NewEvent`]s.
pub trait ConvergentRefinement: Refinement {
    /// The variant type for this refinement. This must be a type that is well-ordered and
    /// well-founded. In other words, every Variant instance must be comparable with every
    /// other one, and there must be no way to create an infinite chain of values where each
    /// value in the chain is less than the previous one.
    type Variant: LexLt;

    /// Map a machine state onto a variant value. Every event in the concrete machine that has no
    /// abstract equivalent must decrease this variant. This prevents a concrete refinement from
    /// deadlocking its abstract equivalent.
    spec fn variant(context: Self::Context, state: Self) -> Self::Variant;
}

/// A `RefinedInit` maps a concrete initialization event to an abstract one. It must specify how to
/// lift the concrete event's input into an input to the abstract event, and it must provide a
/// **simulation proof**. That is, it must prove that initializing a concrete machine then lifting
/// it to the abstract machine produces the same abstract machine as you would get by applying the
/// abstract initialization to the lifted input.
pub trait RefinedInit<M: Refinement, Abstract: Init<M::Abstract>>: Init<M> {
    /// Map a concrete initialization input to an abstract one.
    spec fn lift_in(input: Self::Input) -> Abstract::Input;

    /// Prove that applying the concrete initialization then lifting it to an abstract state
    /// produces the same result as applying the abstract initialization to the lifted concrete
    /// input.
    proof fn proof_simulation(context: M::Context, input: Self::Input)
        requires
            context.valid(),
        ensures
            M::lift(Self::init(context, input)) == Abstract::init(M::lift(context), Self::lift_in(input));
}

/// A `RefinedEvent` maps a concrete event onto an abstract one. It has 4 parts:
/// 1. A way to lift a concrete event input to an abstract one;
/// 2. A way to lift a concrete event output to an abstract one;
/// 3. A **strengthening proof**, which guarantees that the concrete event won't fire in a state in
///    which the abstract event can't fire.
/// 4. A **simulation proof**, which guarantees that applying the concrete event then lifting the
///    result to the abstract representation produces the same abstract state and output as you
///    would get from applying the *abstract* event to a lifted concrete state and input.
pub trait RefinedEvent<M: Refinement, Abstract: Event<M::Abstract>>: Event<M> {
    /// Lift a concrete event input to an abstract one.
    spec fn lift_in(context: M::Context, state: M, input: Self::Input) -> Abstract::Input;

    /// Lift a concrete event output to an abstract one.
    spec fn lift_out(output: Self::Output) -> Abstract::Output;

    /// Prove that the concrete guard cannot be enabled when the abstract guard is not.
    proof fn proof_strengthening(context: M::Context, state: M, input: Self::Input)
        requires
            context.valid(),
            M::invariant(context, state),
            Self::guard(context, state, input),
        ensures
            Abstract::guard(M::lift(context), M::lift(state), Self::lift_in(context, state, input));

    /// Prove that applying the concrete event then lifting the result to an abstract machine state
    /// is equivalent to applying the *abstract* event to the lifted concrete state and input.
    proof fn proof_simulation(context: M::Context, state: M, input: Self::Input)
        requires
            context.valid(),
            M::invariant(context, state),
            Self::guard(context, state, input),
            Abstract::guard(M::lift(context), M::lift(state), Self::lift_in(context, state, input)),
        ensures
            M::lift(Self::action(context, state, input)) == Abstract::action(M::lift(context), M::lift(state), Self::lift_in(context, state, input)),
            Self::lift_out(Self::output(context, state, input)) == Abstract::output(M::lift(context), M::lift(state), Self::lift_in(context, state, input));
}

/// A `NewEvent` is one that appears in a concrete machine which has no counterpart in an abstract
/// machine. A new event must satisfy 2 properties:
/// 1. **Convergence**: the event must decrease the [`Refinement`]'s variant, to prevent new events
///    from deadlocking the abstract machine; and
/// 2. **Stuttering**: the event must not change the abstract representation of the state.
pub trait NewEvent<M: ConvergentRefinement>: Event<M> {
    proof fn proof_convergent(context: M::Context, state: M, input: Self::Input)
        requires
            context.valid(),
            M::invariant(context, state),
            Self::guard(context, state, input),
        ensures
            <M::Variant as LexLt>::lex_lt(
                M::variant(context, Self::action(context, state, input)),
                M::variant(context, state));

    /// Prove that applying the concrete event does not change the lifted abstract state.
    proof fn proof_stuttering(context: M::Context, state: M, input: Self::Input)
        requires
            context.valid(),
            M::invariant(context, state),
            Self::guard(context, state, input),
        ensures
            M::lift(Self::action(context, state, input)) == M::lift(state);
}

/// A `MirrorContext` is the executable context type of a [`Mirror`].
pub trait MirrorContext<M: Lift<Self, SpecContext>, SpecContext: MachineContext>: Sized {
    /// Indicate whether the exec context is valid. Must agree with the lifted spec context.
    exec fn valid(&self) -> (b: bool)
        ensures
            b == M::lift(*self).valid();
}

/// A `Mirror` is an executable type that simulates a spec [`Machine`].
pub trait Mirror<Spec: Machine>:
    Sized + Lift<Self, Spec> + Lift<Self::ExecContext, Spec::Context>
    where Self::ExecContext: MirrorContext<Self, Spec::Context>
{
    /// The executable context type.
    type ExecContext;
}

/// `MirrorEvent` captures the relationship between an executable implementation of an event and
/// its spec mirror. The key property is **bisimulation**: the exec guard should be enabled if and
/// only if the spec guard is enabled on the lifted state, and its action should have a one-to-one
/// relationship with the spec's action.
pub trait MirrorEvent<M: Mirror<Spec>, Spec: Machine, SpecEv: Event<Spec>>
    where M::ExecContext: MirrorContext<M, Spec::Context>
{
    /// The type of input the executable event takes
    type Input;
    /// The type of output the executable event produces
    type Output;

    /// Lift the executable input to a spec input
    spec fn lift_in(input: &Self::Input) -> SpecEv::Input;

    /// Lift the executable output to a spec output
    spec fn lift_out(output: &Self::Output) -> SpecEv::Output;

    /// Indicate whether or not the executable event is enabled. It must be enabled if and only if
    /// the spec guard is enabled on the lifted state.
    exec fn guard(state: &M, context: &M::ExecContext, input: &Self::Input) -> (b: bool)
        ensures
            b == SpecEv::guard(M::lift(*context), M::lift(*state), Self::lift_in(input));

    /// Transform the current exec state to a new state, producing an output. The action and output
    /// must be equivalent to those of the spec mirror.
    exec fn action(state: &M, context: &M::ExecContext, input: &Self::Input) -> (out: (M, Self::Output))
        requires
            SpecEv::guard(M::lift(*context), M::lift(*state), Self::lift_in(input)),
        ensures
            M::lift(out.0) == SpecEv::action(M::lift(*context), M::lift(*state), Self::lift_in(input)),
            Self::lift_out(&out.1) == SpecEv::output(M::lift(*context), M::lift(*state), Self::lift_in(input));
}

/// `MirrorInit` connects an executable initialization with a spec one.
pub trait MirrorInit<M: Mirror<Spec>, Spec: Machine, SpecInit: Init<Spec>>
    where M::ExecContext: MirrorContext<M, Spec::Context>
{
    /// The type of the executable init's input
    type Input;

    /// Transform an executable input to a spec one.
    spec fn lift_in(input: &Self::Input) -> SpecInit::Input;

    /// Initialize the executable state given a context and input.
    exec fn init(context: &M::ExecContext, input: &Self::Input) -> (state: M)
        ensures
            M::lift(state) == SpecInit::init(M::lift(*context), Self::lift_in(input));
}

}

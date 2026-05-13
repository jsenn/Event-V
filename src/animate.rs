//! # Animation
//! 
//! The `animate` module contains some tools to enable interactive debugging of state machines.
//! The term animation is borrowed from Event-B.

/// Contains metadata about a single event.
pub struct EventSpec {
    /// The event's name
    pub name: &'static str,

    /// The inputs (if any) to the event
    pub inputs: Vec<FieldSpec>,
}

/// Contains metadata about a field within a struct used by a machine.
pub struct FieldSpec {
    /// The field's name
    pub name: &'static str,

    /// Human-readable name of the field's type
    pub kind: &'static str,
}

/// Contains metadata about a machine's `Context` object.
pub trait ContextAdaptor: Sized {
    /// Returns the fields of a machine's Context struct.
    fn fields() -> Vec<FieldSpec>;

    /// Builds a `ContextAdaptor` from a given set of inputs for its fields.
    fn build(inputs: &[String]) -> Result<Self, String>;
}

/// Contains metadata about all events supported by a machine.
pub trait EventAdaptor: Sized {
    /// Returns the event spec for every event supported by the machine.
    fn variants() -> Vec<EventSpec>;

    /// Constructs an event given its name and appropriate inputs.
    /// 
    /// # Errors
    /// If the event name is unrecognized or the inputs do not match the event's expectations, an
    /// error message is produced.
    fn build(name: &str, inputs: &[String]) -> Result<Self, String>;
}

/// Contains the necessary glue to animate a machine.
pub trait Animate: Sized {
    /// The `ContextAdaptor` for this animated machine
    type Ctx: ContextAdaptor;

    /// The event enum for this animated machine
    type Event: EventAdaptor;

    /// Create an animation given a context.
    fn init(ctx: &Self::Ctx) -> Self;

    /// Execute the appropriate guard for a given event.
    fn guard(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> bool;

    /// Apply a given event's action, returning the new state and an optional formatted output.
    fn action(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> (Self, Option<String>);
}

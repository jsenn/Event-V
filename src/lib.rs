//! # Verus Machine
//! 
//! `verus_machine` provides a framework and syntax for defining state machines. It formalizes
//! state machine **refinement** and provides tools to debug state machines during development.
//! 
//! As its name suggests, `verus_machine` is built on the Verus formal verification framework.

/// The `machine` module contains the trait machinery underlying `verus_machine`.
pub mod machine;

/// The `animate` module contains some plumbing to interactively debug state machines.
pub mod animate;

/// The `verus_machine_macros` crate provides a proc macro that provides convenient syntactic sugar
/// on top of the trait machinery in `machine`, which can be quite verbose.
pub use verus_machine_macros::verus_machine;

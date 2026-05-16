//! # Event V
//!
//! `event_v` provides a framework and syntax for defining state machines. It formalizes
//! state machine **refinement** and provides tools to debug state machines during development.
//!
//! As its name suggests, `event_v` is built on the Verus formal verification framework.

/// The `machine` module contains the trait machinery underlying `event_v`.
pub mod machine;

/// The `lex_lt` module defines the [`lex_lt::LexLt`] trait and some standard impls.
pub mod lex_lt;

/// The `animate` module contains some plumbing to interactively debug state machines.
pub mod animate;

/// The `event_v_macros` crate provides a proc macro that provides convenient syntactic sugar
/// on top of the trait machinery in `machine`, which can be quite verbose.
pub use event_v_macros::machine;

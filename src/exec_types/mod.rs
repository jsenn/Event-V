//! Executable mirrors of Verus ghost types.
//!
//! Verus spec types (`nat`, `int`, `Seq<T>`, `Set<T>`, `Map<K,V>`, ...) are
//! erased during normal compilation, so the animation layer needs concrete
//! runtime types that expose the same API. These types are wrappers over
//! `num::BigInt` / `Vec` / `HashSet` / `HashMap` that mimic the shape of
//! `vstd`'s spec API (`.push`, `.subrange`, `.insert`, ...) so user bodies
//! like `state.data.subrange(1, state.data.len() as int)` compile verbatim
//! (after `as int` / `as nat` casts are stripped).

pub mod nat;
pub mod parse_input;
pub mod sample;
pub mod seq;

pub use nat::Nat;
pub use parse_input::ParseInput;
pub use sample::Sample;
pub use seq::{IntoIdx, Seq};

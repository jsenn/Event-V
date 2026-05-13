//! # LexLt
//!
//! A well-founded strict order on variant types, used by [`crate::machine::Refinement`] to
//! declare the order that new events must decrease.
//!
//! Standard impls are provided for `nat` and tuples of `nat` up to arity 16, all defined via
//! Verus's built-in `decreases_to!` (so they are well-founded by construction). Parallel impls
//! for `bool` and tuples of `bool` are also provided.

use vstd::prelude::*;

verus! {

/// A well-founded strict order on `Self`.
pub trait LexLt: Sized {
    /// Returns true iff `a` is strictly less than `b` in this type's lex order.
    spec fn lex_lt(a: Self, b: Self) -> bool;
}

impl LexLt for nat {
    open spec fn lex_lt(a: nat, b: nat) -> bool {
        decreases_to!(b => a)
    }
}

impl LexLt for (nat, nat) {
    open spec fn lex_lt(a: (nat, nat), b: (nat, nat)) -> bool {
        decreases_to!(b.0, b.1 => a.0, a.1)
    }
}

impl LexLt for (nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat), b: (nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2 => a.0, a.1, a.2)
    }
}

impl LexLt for (nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat), b: (nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3 => a.0, a.1, a.2, a.3)
    }
}

impl LexLt for (nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4 => a.0, a.1, a.2, a.3, a.4)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5 => a.0, a.1, a.2, a.3, a.4, a.5)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6 => a.0, a.1, a.2, a.3, a.4, a.5, a.6)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10, b.11 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10, a.11)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10, b.11, b.12 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10, a.11, a.12)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10, b.11, b.12, b.13 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10, a.11, a.12, a.13)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10, b.11, b.12, b.13, b.14 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10, a.11, a.12, a.13, a.14)
    }
}

impl LexLt for (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) {
    open spec fn lex_lt(a: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat), b: (nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat)) -> bool {
        decreases_to!(b.0, b.1, b.2, b.3, b.4, b.5, b.6, b.7, b.8, b.9, b.10, b.11, b.12, b.13, b.14, b.15 => a.0, a.1, a.2, a.3, a.4, a.5, a.6, a.7, a.8, a.9, a.10, a.11, a.12, a.13, a.14, a.15)
    }
}

/// Map a bool to a nat: `false -> 0`, `true -> 1`.
pub open spec fn b2n(b: bool) -> nat { if b { 1nat } else { 0nat } }

impl LexLt for bool {
    open spec fn lex_lt(a: bool, b: bool) -> bool {
        <nat as LexLt>::lex_lt(b2n(a), b2n(b))
    }
}

impl LexLt for (bool, bool) {
    open spec fn lex_lt(a: (bool, bool), b: (bool, bool)) -> bool {
        <(nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1)),
            (b2n(b.0), b2n(b.1)),
        )
    }
}

impl LexLt for (bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool), b: (bool, bool, bool)) -> bool {
        <(nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2)),
            (b2n(b.0), b2n(b.1), b2n(b.2)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool), b: (bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10), b2n(a.11)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10), b2n(b.11)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10), b2n(a.11), b2n(a.12)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10), b2n(b.11), b2n(b.12)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10), b2n(a.11), b2n(a.12), b2n(a.13)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10), b2n(b.11), b2n(b.12), b2n(b.13)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10), b2n(a.11), b2n(a.12), b2n(a.13), b2n(a.14)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10), b2n(b.11), b2n(b.12), b2n(b.13), b2n(b.14)),
        )
    }
}

impl LexLt for (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
    open spec fn lex_lt(a: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool), b: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)) -> bool {
        <(nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat) as LexLt>::lex_lt(
            (b2n(a.0), b2n(a.1), b2n(a.2), b2n(a.3), b2n(a.4), b2n(a.5), b2n(a.6), b2n(a.7), b2n(a.8), b2n(a.9), b2n(a.10), b2n(a.11), b2n(a.12), b2n(a.13), b2n(a.14), b2n(a.15)),
            (b2n(b.0), b2n(b.1), b2n(b.2), b2n(b.3), b2n(b.4), b2n(b.5), b2n(b.6), b2n(b.7), b2n(b.8), b2n(b.9), b2n(b.10), b2n(b.11), b2n(b.12), b2n(b.13), b2n(b.14), b2n(b.15)),
        )
    }
}

}

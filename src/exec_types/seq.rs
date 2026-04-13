//! Executable mirror of Verus `Seq<T>`.
//!
//! Wraps `Vec<T>` with the subset of the `vstd::seq::Seq` API we need to let
//! user bodies (`state.data.subrange(1, state.data.len() as int)`, etc.)
//! compile and execute. Methods that create new sequences (`push`, `update`,
//! `add`) consume `self` by value and return a fresh `Seq`, matching Verus's
//! immutable semantics.

use num::ToPrimitive;
use std::fmt;
use std::ops::Index;

use super::nat::Nat;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Seq<T> {
    pub(crate) inner: Vec<T>,
}

// -----------------------------------------------------------------------------
// IntoIdx: flexible integer conversion for indexing / range arguments.
//
// Verus spec code uses `int` and `nat` freely for indices; `as int` / `as nat`
// casts are stripped by the body transformer, so downstream we see a mix of
// raw integer types (i32 from literals, Nat from .len(), etc.). This trait
// lets `.subrange`, `.take`, `.skip`, `[i]` accept any of them without callers
// having to insert conversions.
// -----------------------------------------------------------------------------

pub trait IntoIdx {
    fn into_idx(self) -> usize;
}

impl IntoIdx for usize {
    fn into_idx(self) -> usize {
        self
    }
}
impl IntoIdx for i32 {
    fn into_idx(self) -> usize {
        assert!(self >= 0, "negative index");
        self as usize
    }
}
impl IntoIdx for i64 {
    fn into_idx(self) -> usize {
        assert!(self >= 0, "negative index");
        self as usize
    }
}
impl IntoIdx for u32 {
    fn into_idx(self) -> usize {
        self as usize
    }
}
impl IntoIdx for u64 {
    fn into_idx(self) -> usize {
        self as usize
    }
}
impl IntoIdx for Nat {
    fn into_idx(self) -> usize {
        self.0.to_usize().expect("index too large")
    }
}
impl IntoIdx for &Nat {
    fn into_idx(self) -> usize {
        self.0.to_usize().expect("index too large")
    }
}

// -----------------------------------------------------------------------------
// Seq constructors and core API
// -----------------------------------------------------------------------------

impl<T> Seq<T> {
    pub fn empty() -> Self {
        Seq { inner: Vec::new() }
    }

    /// Build a `Seq` directly from a `Vec`. This is what the `seq![...]`
    /// macro lowers to.
    pub fn from_vec(v: Vec<T>) -> Self {
        Seq { inner: v }
    }

    pub fn len(&self) -> Nat {
        Nat::from(self.inner.len())
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl<T: Clone> Seq<T> {
    /// `Seq::new(len, f)` — element `i` is `f(i)`.
    pub fn new<I, F>(len: I, f: F) -> Self
    where
        I: IntoIdx,
        F: Fn(Nat) -> T,
    {
        let n = len.into_idx();
        let mut v = Vec::with_capacity(n);
        for i in 0..n {
            v.push(f(Nat::from(i)));
        }
        Seq { inner: v }
    }

    pub fn singleton(x: T) -> Self {
        Seq { inner: vec![x] }
    }

    /// Append one element, returning a new `Seq` (Verus semantics).
    pub fn push(mut self, x: T) -> Self {
        self.inner.push(x);
        self
    }

    /// Replace the element at `i`, returning a new `Seq`.
    pub fn update<I: IntoIdx>(mut self, i: I, x: T) -> Self {
        self.inner[i.into_idx()] = x;
        self
    }

    /// Index lookup that accepts any `IntoIdx` — used by the animate codegen
    /// for `seq[i]` expressions, where `Index` impls would be ambiguous for
    /// bare integer literals like `0`.
    pub fn at<I: IntoIdx>(&self, i: I) -> &T {
        &self.inner[i.into_idx()]
    }

    /// Slice `[start, end)`.
    pub fn subrange<I1: IntoIdx, I2: IntoIdx>(&self, start: I1, end: I2) -> Self {
        let s = start.into_idx();
        let e = end.into_idx();
        Seq {
            inner: self.inner[s..e].to_vec(),
        }
    }

    pub fn take<I: IntoIdx>(&self, n: I) -> Self {
        let n = n.into_idx();
        Seq {
            inner: self.inner[..n].to_vec(),
        }
    }

    pub fn skip<I: IntoIdx>(&self, n: I) -> Self {
        let n = n.into_idx();
        Seq {
            inner: self.inner[n..].to_vec(),
        }
    }

    /// Concatenation.
    pub fn add(mut self, rhs: Seq<T>) -> Self {
        self.inner.extend(rhs.inner);
        self
    }

    pub fn first(&self) -> T {
        self.inner[0].clone()
    }

    pub fn last(&self) -> T {
        self.inner
            .last()
            .expect("last() on empty Seq")
            .clone()
    }

    pub fn drop_first(&self) -> Self {
        self.skip(1usize)
    }

    pub fn drop_last(&self) -> Self {
        self.take(self.inner.len() - 1)
    }

    pub fn reverse(&self) -> Self {
        let mut v = self.inner.clone();
        v.reverse();
        Seq { inner: v }
    }
}

impl<T: Clone + PartialEq> Seq<T> {
    pub fn contains(&self, x: &T) -> bool {
        self.inner.contains(x)
    }

    /// Index of `x` or `-1` if absent (matches `vstd::seq_lib` convention).
    pub fn index_of(&self, x: &T) -> i64 {
        self.inner.iter().position(|e| e == x).map(|i| i as i64).unwrap_or(-1)
    }
}

// -----------------------------------------------------------------------------
// Indexing — one impl per integer type we expect to meet in user code
// -----------------------------------------------------------------------------

macro_rules! impl_seq_index {
    ($($t:ty),*) => {
        $(
            impl<T> Index<$t> for Seq<T> {
                type Output = T;
                fn index(&self, i: $t) -> &T {
                    &self.inner[IntoIdx::into_idx(i)]
                }
            }
        )*
    };
}
impl_seq_index!(usize, i32, i64, u32, u64);

impl<T> Index<Nat> for Seq<T> {
    type Output = T;
    fn index(&self, i: Nat) -> &T {
        &self.inner[i.into_idx()]
    }
}
impl<T> Index<&Nat> for Seq<T> {
    type Output = T;
    fn index(&self, i: &Nat) -> &T {
        &self.inner[i.into_idx()]
    }
}

// -----------------------------------------------------------------------------
// Conversions and formatting
// -----------------------------------------------------------------------------

impl<T> From<Vec<T>> for Seq<T> {
    fn from(v: Vec<T>) -> Self {
        Seq { inner: v }
    }
}

impl<T> IntoIterator for Seq<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Seq<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for Seq<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(&self.inner).finish()
    }
}

impl<T: fmt::Display> fmt::Display for Seq<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, x) in self.inner.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", x)?;
        }
        write!(f, "]")
    }
}

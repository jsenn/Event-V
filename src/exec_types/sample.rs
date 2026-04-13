//! `Sample` — random value generation for animation / fuzzing.
//!
//! An event with `type Input = nat` needs some way to produce a concrete
//! `Nat` when the animator steps randomly. Types implement `Sample` to
//! provide a default distribution; users can override by writing their own
//! `random_event` if the default range is unsuitable.

use rand::Rng;

use super::nat::Nat;

pub trait Sample: Sized {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self;
}

impl Sample for () {
    fn sample<R: Rng + ?Sized>(_: &mut R) -> Self {
        ()
    }
}

impl Sample for bool {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen()
    }
}

/// Default `Nat` sampler — small non-negative integers (0..100).
/// For a custom range, implement `random_event` directly on the machine.
impl Sample for Nat {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Nat::from(rng.gen_range(0u64..100))
    }
}

impl Sample for u32 {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen_range(0..100)
    }
}

impl Sample for u64 {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen_range(0..100)
    }
}

impl Sample for i32 {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen_range(-50..50)
    }
}

impl Sample for i64 {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen_range(-50..50)
    }
}

impl Sample for usize {
    fn sample<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.gen_range(0..100)
    }
}

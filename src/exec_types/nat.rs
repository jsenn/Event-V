use num::BigInt;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Sub};
use std::str::FromStr;

/// Executable representation of Verus `nat` — an arbitrary-precision non-negative integer.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Nat(pub BigInt);

impl fmt::Debug for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Nat {
    pub fn new(val: u64) -> Self {
        Nat(BigInt::from(val))
    }
}

// --- Display ---

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// --- Ord ---

impl Ord for Nat {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// --- Comparison with i32 (default integer literal type) ---

impl PartialEq<i32> for Nat {
    fn eq(&self, other: &i32) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialOrd<i32> for Nat {
    fn partial_cmp(&self, other: &i32) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

// --- Comparison with u64 ---

impl PartialEq<u64> for Nat {
    fn eq(&self, other: &u64) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialOrd<u64> for Nat {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

// --- Arithmetic: Nat op Nat ---

impl Add for Nat {
    type Output = Nat;
    fn add(self, rhs: Nat) -> Nat {
        Nat(self.0 + rhs.0)
    }
}

impl Sub for Nat {
    type Output = Nat;
    fn sub(self, rhs: Nat) -> Nat {
        Nat(self.0 - rhs.0)
    }
}

// --- Arithmetic: &Nat op &Nat ---

impl Add for &Nat {
    type Output = Nat;
    fn add(self, rhs: &Nat) -> Nat {
        Nat(&self.0 + &rhs.0)
    }
}

impl Sub for &Nat {
    type Output = Nat;
    fn sub(self, rhs: &Nat) -> Nat {
        Nat(&self.0 - &rhs.0)
    }
}

// --- Arithmetic: Nat op &Nat, &Nat op Nat ---

impl Add<&Nat> for Nat {
    type Output = Nat;
    fn add(self, rhs: &Nat) -> Nat {
        Nat(self.0 + &rhs.0)
    }
}

impl Sub<&Nat> for Nat {
    type Output = Nat;
    fn sub(self, rhs: &Nat) -> Nat {
        Nat(self.0 - &rhs.0)
    }
}

impl Add<Nat> for &Nat {
    type Output = Nat;
    fn add(self, rhs: Nat) -> Nat {
        Nat(&self.0 + rhs.0)
    }
}

impl Sub<Nat> for &Nat {
    type Output = Nat;
    fn sub(self, rhs: Nat) -> Nat {
        Nat(&self.0 - rhs.0)
    }
}

// --- Arithmetic: Nat op i32 ---

impl Add<i32> for Nat {
    type Output = Nat;
    fn add(self, rhs: i32) -> Nat {
        Nat(self.0 + BigInt::from(rhs))
    }
}

impl Sub<i32> for Nat {
    type Output = Nat;
    fn sub(self, rhs: i32) -> Nat {
        Nat(self.0 - BigInt::from(rhs))
    }
}

// --- Arithmetic: &Nat op i32 ---

impl Add<i32> for &Nat {
    type Output = Nat;
    fn add(self, rhs: i32) -> Nat {
        Nat(&self.0 + BigInt::from(rhs))
    }
}

impl Sub<i32> for &Nat {
    type Output = Nat;
    fn sub(self, rhs: i32) -> Nat {
        Nat(&self.0 - BigInt::from(rhs))
    }
}

// --- Arithmetic: Nat op u64 ---

impl Add<u64> for Nat {
    type Output = Nat;
    fn add(self, rhs: u64) -> Nat {
        Nat(self.0 + BigInt::from(rhs))
    }
}

impl Sub<u64> for Nat {
    type Output = Nat;
    fn sub(self, rhs: u64) -> Nat {
        Nat(self.0 - BigInt::from(rhs))
    }
}

// --- Arithmetic: &Nat op u64 ---

impl Add<u64> for &Nat {
    type Output = Nat;
    fn add(self, rhs: u64) -> Nat {
        Nat(&self.0 + BigInt::from(rhs))
    }
}

impl Sub<u64> for &Nat {
    type Output = Nat;
    fn sub(self, rhs: u64) -> Nat {
        Nat(&self.0 - BigInt::from(rhs))
    }
}

// --- From conversions ---

impl From<i32> for Nat {
    fn from(val: i32) -> Self {
        Nat(BigInt::from(val))
    }
}

impl From<u64> for Nat {
    fn from(val: u64) -> Self {
        Nat(BigInt::from(val))
    }
}

impl From<usize> for Nat {
    fn from(val: usize) -> Self {
        Nat(BigInt::from(val))
    }
}

// --- FromStr ---

impl FromStr for Nat {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bi: BigInt = s.parse().map_err(|e: num::bigint::ParseBigIntError| e.to_string())?;
        if bi < BigInt::from(0) {
            return Err("nat must be non-negative".into());
        }
        Ok(Nat(bi))
    }
}

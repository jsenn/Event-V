use vstd::prelude::*;

 verus! {

/// Represents a valid roll of a six-sided die. This uses Verus's `type_invariant` feature to
/// make sure every instance is valid by construction.
 pub struct DiceRoll {
    value: u8,
 }

 /// Define the invariant for a valid `DiceRoll`--namely, that its value be between 1 and 6.
#[verifier::type_invariant]
pub open spec fn dice_roll_valid(d: DiceRoll) -> bool {
    1 <= d.value() <= 6
}

impl DiceRoll {
    /// A constructor that can be used in `exec` mode.
    pub fn new(n: u8) -> (r: Option<DiceRoll>)
        ensures
            r matches Some(d) ==> 1 <= d.value() <= 6,
    {
        if 1 <= n && n <= 6 {
            Some(DiceRoll { value: n })
        } else {
            None
        }
    }

    /// Retrieve the value in spec mode.
    pub closed spec fn value(&self) -> nat {
        self.value as nat
    }
}

}
use vstd::prelude::*;

 verus! {

 pub struct DiceRoll {
    value: u8,
 }

#[verifier::type_invariant]
pub open spec fn dice_roll_valid(d: DiceRoll) -> bool {
    1 <= d.value() <= 6
}

impl DiceRoll {
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

    pub closed spec fn value(&self) -> nat {
        self.value as nat
    }
}

}
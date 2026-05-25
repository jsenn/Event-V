//! Here we define a simple [`DiceRoll`] helper that represents a valid roll of a single die.

use vstd::prelude::*;

 verus! {

/// Represents a roll of a six-sided die.
 pub enum DiceRoll { One, Two, Three, Four, Five, Six, }

impl DiceRoll {
    /// Retrieve the numeric value of a [`DiceRoll`]
    pub open spec fn value(self) -> nat {
        match self {
            DiceRoll::One => 1,
            DiceRoll::Two => 2,
            DiceRoll::Three => 3,
            DiceRoll::Four => 4,
            DiceRoll::Five => 5,
            DiceRoll::Six => 6,
        }
    }
}

}
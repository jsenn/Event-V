use vstd::prelude::*;

verus! {

pub enum TrafficLight {
    Red,
    Green,
}

impl TrafficLight {
    pub open spec fn is_red(&self) -> bool {
        matches!(*self, TrafficLight::Red)
    }

    pub open spec fn is_green(&self) -> bool {
        matches!(*self, TrafficLight::Green)
    }
}

} // verus!

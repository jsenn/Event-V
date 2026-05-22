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

pub enum Flag {
    Set,
    Clear,
}

impl Flag {
    pub open spec fn is_set(&self) -> bool {
        matches!(*self, Flag::Set)
    }

    pub open spec fn is_clear(&self) -> bool {
        matches!(*self, Flag::Clear)
    }
}

pub enum Sensor {
    On,
    Off,
}

impl Sensor {
    pub open spec fn is_on(&self) -> bool {
        matches!(*self, Sensor::On)
    }

    pub open spec fn is_off(&self) -> bool {
        matches!(*self, Sensor::Off)
    }
}

} // verus!

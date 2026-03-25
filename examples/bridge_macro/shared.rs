use vstd::prelude::*;

use verus_machine::machine::MachineContext;

verus! {

#[allow(dead_code)]
pub struct BridgeCtx {
    pub max_cars: nat,
}

impl MachineContext for BridgeCtx {
    open spec fn valid(&self) -> bool {
        self.max_cars > 0
    }
}

} // verus!

/// Executable context for animation. Mirrors BridgeCtx with exec types.
#[derive(Debug, Clone)]
pub struct BridgeCtxExec {
    pub max_cars: verus_machine::exec_types::Nat,
}

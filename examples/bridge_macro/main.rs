mod shared;
mod abs;
mod ref1;

fn main() {
    #[cfg(not(verus_only))]
    {
        use verus_machine::animate::Animate;
        use verus_machine::exec_types::Nat;

        let ctx = shared::BridgeCtxExec { max_cars: Nat::from(3) };
        ref1::animate::Ref1::run(ctx);
    }
}

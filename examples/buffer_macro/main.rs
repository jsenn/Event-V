mod buf0;
mod buf1;

fn main() {
    #[cfg(not(verus_only))]
    {
        use verus_machine::animate::Animate;
        use verus_machine::exec_types::Nat;

        let ctx = buf0::animate::Ctx { max_size: Nat::from(3) };
        buf1::animate::Buf1::run(ctx);
    }
}

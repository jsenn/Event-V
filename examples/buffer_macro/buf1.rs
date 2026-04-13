use vstd::prelude::*;

use crate::buf0;

use verus_machine::machine::*;
use verus_machine::verus_machine;

verus_machine! {

machine Buf1 refines buf0::Buf0 {
    ctx: buf0::Ctx,

    state {
        data: Seq<nat>,
    }

    init(ctx) {
        data: Seq::empty()
    }

    lift(state) {
        buf0::Buf0 {
            size: state.data.len(),
        }
    }

    refined event Put(elem: nat) {
        guard(ctx, state) {
            state.data.len() < ctx.max_size
        }

        action(ctx, state) {
            Buf1 {
                data: seq![elem].add(state.data),
            }
        }

        lift_in(_elem) { () }
    }

    refined event Fetch -> nat {
        guard(ctx, state) {
            state.data.len() > 0
        }

        action(ctx, state) {
            Buf1 {
                data: state.data.subrange(1, state.data.len() as int),
            }
        }

        output(ctx, state) {
            state.data[0]
        }

        lift_out(_n) { () }
    }

    refined event GetSize -> nat {
        guard(ctx, state) {
            true
        }

        action(ctx, state) {
            state
        }

        output(ctx, state) {
            state.data.len()
        }

        lift_out(n) { n }
    }
}

}

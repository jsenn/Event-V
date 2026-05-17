use vstd::prelude::*;

use crate::buf0;

use event_v::machine::*;
use event_v::machine;

machine! {

machine Buf1 refines buf0::Buf0 {
    context: buf0::Context,

    state {
        data: Seq<nat>,
    }

    init: |context| Buf1 { data: Seq::empty() },

    lift: |state| buf0::Buf0 { size: state.data.len() },

    refined event Put(elem: nat) {
        guard: |context, state| state.data.len() < context.max_size,
        action: |context, state| Buf1 { data: seq![elem].add(state.data) },
        lift_in: |_context, _state| (),
    }

    refined event Fetch -> nat {
        guard: |context, state| state.data.len() > 0,
        action: |context, state| Buf1 {
            data: state.data.subrange(1, state.data.len() as int),
        },
        output: |context, state| state.data[0],
        lift_out: |_n| (),
    }

    refined event GetSize -> nat {
        guard: |context, state| true,
        action: |context, state| state,
        output: |context, state| state.data.len(),
        lift_out: |n| n,
    }
}

}

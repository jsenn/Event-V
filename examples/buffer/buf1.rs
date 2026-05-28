//! In this refinement of the [abstract buffer model][`buf0::Buf0`], we model the buffer's contents
//! as a sequence of natural numbers.
//! 
//! We are now able to add an input to the [`Put`] event, and produce an output from [`Fetch`].
//! This buffer has FIFO semantics. We equally well could define a LIFO refinement, or even
//! something more exotic like a priority queue.

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

    init: |context| Buf1 { data: Seq::empty() }

    lift: |state| buf0::Buf0 { size: state.data.len() }

    // Append the given element to the end of the buffer.
    refined event Put(elem: nat) {
        guard: |context, state| state.data.len() < context.max_size
        action: |context, state| Buf1 { data: seq![elem].add(state.data) }
        lift_in: |_context, _state| ()
    }

    // Remove and return the buffer's first element.
    refined event Fetch -> nat {
        guard: |context, state| state.data.len() > 0
        action: |context, state| Buf1 {
            data: state.data.subrange(1, state.data.len() as int),
        }
        output: |context, state| state.data[0]
        lift_out: |_n| ()
    }

    refined event GetSize -> nat {
        guard: |context, state| true
        action: |context, state| state
        output: |context, state| state.data.len()
        lift_out: |n| n
    }
}

}

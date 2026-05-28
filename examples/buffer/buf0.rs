//! The abstract buffer tracks only the current size of the buffer, and maintains the invariant
//! that its size never exceed the configured max size.
//!
//! Note that the [`Put`] event doesn't yet take an input to put in the buffer, and the [`Fetch`]
//! event doesn't produce any output. That is perfectly fine, and the next refinement will add
//! inputs and outputs.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

machine! {

deadlock_free machine Buf0 {
    context {
        max_size: nat,
    }

    valid: |context| context.max_size > 0

    state {
        size: nat,
    }

    init: |context| Buf0 { size: 0 }

    invariant: |context, state| state.size <= context.max_size

    event Put {
        guard: |context, state| state.size < context.max_size
        action: |context, state| Buf0 { size: state.size + 1 }
    }

    event Fetch {
        guard: |context, state| state.size > 0
        action: |context, state| Buf0 { size: (state.size - 1) as nat }
    }

    event GetSize -> nat {
        guard: |context, state| true
        action: |context, state| state
        output: |context, state| state.size
    }
}

}

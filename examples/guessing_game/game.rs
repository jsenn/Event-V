//! A formalization of the Guessing Game in Chapter 2 of The Rust Programming Language.

use vstd::prelude::*;

use event_v::machine::*;
use event_v::machine;

verus! {

pub enum Feedback {
    TooSmall,
    TooBig,
    YouWin,
}

}

machine! {

machine Game {
    context {
        secret_number: nat,
    }

    valid: |context| 1 <= context.secret_number <= 100

    state {
        won: bool,
    }

    init: |context| Game { won: false }

    event Guess(guess: nat) -> (feedback: Feedback) {
        guard: |context, state| !state.won
        action: |context, state| Game { won: guess == context.secret_number }
        output: |context, state| {
            if guess < context.secret_number {
                Feedback::TooSmall
            } else if guess > context.secret_number {
                Feedback::TooBig
            } else {
                Feedback::YouWin
            }
        }
        ensures: |context, before, after|
            (feedback == Feedback::YouWin) <==> after.won
    }
}

}

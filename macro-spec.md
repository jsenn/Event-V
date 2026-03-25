The existing framework in `src/` is functional for creating event-driven specs of systems that can be used to verify executable implementations. However, it has a couple of limitations:
1. The trait definitions are very verbose. In particular, having to write out the almost-always-empty proofs is tedious.
2. Because this is all spec/proof code, it's hard to visualize/debug the machines.

The first is easily solvable with some simple macros, but the second is more fundamental. A nice feature of Event-B is "animation", which allows the user to step through a simulation of the abstract machine to gain intuition on how it behaves. Because everything in the current framework is done in spec code, it's not currently possible to implement an animation system like this.

I would like to propose a new proc macro `verus_machine!`. It enables some new syntax to make defining machines easier. For example, the machine in `examples/bridge/abs.rs` might look something like the following.

```rust
verus_machine! {

deadlock_free machine Abs {
    ctx: BridgeCtx,

    state {
        cars: nat,
    }

    init(ctx) {
        cars: 0
    }

    invariant(ctx, state) {
        state.cars <= ctx.max_cars
    }

    event MainlandIn {
        guard(ctx, state) {
            state.cars > 0
        }

        action(ctx, state) {
            Abs {
                cars: (state.cars - 1) as nat,
                ..state
            }
        }
    }

    event MainlandOut {
        guard(ctx, state) {
            state.cars < ctx.max_cars
        }

        action(ctx, state) {
            Abs {
                cars: state.cars + 1,
                ..state
            }
        }
    }
}

}
```

And `examples/bridge/ref1.rs` would like something like the following.

```rust
verus_machine! {

deadlock_free machine Ref1 refines Abs {
    ctx: BridgeCtx

    state {
        cars_to_island: nat,
        cars_on_island: nat,
        cars_to_mainland: nat,
    }

    init(ctx) {
        cars_to_island: 0,
        cars_on_island: 0,
        cars_to_mainland: 0,
    }

    lift(state) {
        Abs {
            cars: state.total_cars(),
        }
    }

    invariant(ctx, state) {
        // Abs::invariant(lift(state)) is implicitly required
        state.cars_to_island == 0 || state.cars_to_mainland == 0
    }

    refined event MainlandIn {
        guard(ctx, state) {
            state.cars_to_mainland > 0
        }

        action(ctx, state) {
            Ref1 {
                cars_to_mainland: (state.cars_to_mainland - 1) as nat,
                ..state
            }
        }
    }

    refined event MainlandOut {
        guard(ctx, state) {
            &&& state.cars_to_mainland == 0
            &&& state.total_cars() < ctx.max_cars
        }

        action(ctx, state) {
            Ref1 {
                cars_to_island: state.cars_to_mainland + 1,
                ..state
            }
        }
    }

    // concrete events have a proof_stuttering and must be convergent
    concrete convergent event IslandIn {
        guard(ctx, state) {
            state.cars_to_island > 0
        }

        action(ctx, state) {
            Ref1 {
                cars_to_island: (state.cars_to_island - 1) as nat,
                cars_on_island: state.cars_on_island + 1,
                ..state
            }
        }

        variant(ctx, state) {
            state.cars_to_island
        }
    }

    concrete convergent event IslandOut {
        guard(ctx, state) {
            &&& state.cars_on_island > 0
            &&& state.cars_to_island == 0
        }

        action(ctx, state) {
            Ref1 {
                cars_on_island: (state.cars_on_island - 1) as nat,
                cars_to_mainland: state.cars_to_mainland + 1,
                ..state
            }
        }

        variant(ctx, state) {
            state.cars_on_island
        }
    }
}

}
```

Note that proofs are omitted. However, it should be possible to specify all proofs as needed. If you forget to refine an abstract event in a refined machine, you get an error. If you try to introduce a concrete event without a variant, error.

The result of the proc macro is the trait definitions for speccing, but an animation module has to be able to consume it somehow to allow the user to interactively step through a simulation of their machine to gain some intuition. I don't know how that should work yet, but it's an important requirement.

# Unanswered questions
* How is the State::verify pattern handled?
* How are auxiliary functions like total_cars() defined?

# Details
* Use the `verus_syn` crate to parse verus syntax in function bodies
* Abstract types like `int` should have executable implementations that can handle most cases. For example, `int` should be a `num::BigInt`. `Seq` can be represented with a `Vec`, etc. Sets and maps are a little harder as technically they can be infinite, but let's ignore that for the time being and use `HashMap` and `HashSet` for now.
* Quantifiers are trickier, let's ignore them for now.
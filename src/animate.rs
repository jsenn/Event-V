//! Interactive animation / random-stepping runner for state machines.
//!
//! Each generated machine's `animate` module provides an impl of this trait
//! with:
//!   * an `Event` enum whose variants carry their event's `Input` as a
//!     payload (for inputless events, the variant is a unit variant);
//!   * an `event_menu()` that describes the available events and, for each,
//!     the names / type-kinds of their input fields (used by the interactive
//!     loop to prompt the user);
//!   * `construct_event` / `random_event` to build `Event` values from
//!     user-typed strings or from a random `Sample` impl.

use rand::seq::SliceRandom;
use rand::Rng;
use std::fmt;
use std::io::{self, Write};

/// Metadata describing a single event's input surface.
///
/// Used by `run()` to prompt the user. The `name` is the event's Rust
/// variant name (e.g. `"Put"`); `inputs` is empty for inputless events.
pub struct EventSpec {
    pub name: &'static str,
    pub inputs: Vec<InputSpec>,
}

/// Metadata for one input field on an event.
///
/// `ty_kind` is a short label shown in prompts (`"nat"`, `"bool"`, ...).
/// Parsing is event-specific and happens in `construct_event`.
pub struct InputSpec {
    pub name: &'static str,
    pub ty_kind: &'static str,
}

pub trait Animate: Clone + fmt::Display {
    type Ctx;
    type Event: Clone + fmt::Display + fmt::Debug;

    fn init(ctx: &Self::Ctx) -> Self;

    /// Describe all events (for building the menu / prompts).
    fn event_menu() -> Vec<EventSpec>;

    /// Build an `Event` from a name and a slice of user-typed input strings.
    /// Returns an error message on parse failure or unknown name.
    fn construct_event(name: &str, inputs: &[String]) -> Result<Self::Event, String>;

    /// Build an `Event` with randomly-sampled inputs. The returned event
    /// may or may not be currently enabled — callers should check `guard`
    /// and retry / give up as appropriate.
    fn random_event<R: Rng + ?Sized>(rng: &mut R) -> Self::Event;

    fn guard(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> bool;
    fn action(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> Self;

    /// Evaluate the event's `output` body on the pre-action state, formatted
    /// for display. Returns `None` for events that declare no output.
    fn output(_ctx: &Self::Ctx, _state: &Self, _event: &Self::Event) -> Option<String> {
        None
    }

    /// Try to find a random enabled event by sampling up to `tries` times
    /// per event variant. Returns `None` if nothing fires within the budget.
    fn random_enabled_event<R: Rng + ?Sized>(
        ctx: &Self::Ctx,
        state: &Self,
        rng: &mut R,
        tries: usize,
    ) -> Option<Self::Event> {
        // Try uniformly-random events first; if the input distribution
        // rarely hits enabled inputs this may fail quickly, so we fall back
        // to walking the menu in shuffled order.
        for _ in 0..tries {
            let evt = Self::random_event(rng);
            if Self::guard(ctx, state, &evt) {
                return Some(evt);
            }
        }
        let mut menu = Self::event_menu();
        menu.shuffle(rng);
        for spec in &menu {
            if spec.inputs.is_empty() {
                // Inputless: construct directly via construct_event (only
                // one possible variant, so no sampling needed).
                if let Ok(evt) = Self::construct_event(spec.name, &[]) {
                    if Self::guard(ctx, state, &evt) {
                        return Some(evt);
                    }
                }
            } else {
                for _ in 0..tries {
                    let evt = Self::random_event(rng);
                    if format!("{:?}", evt).starts_with(spec.name)
                        && Self::guard(ctx, state, &evt)
                    {
                        return Some(evt);
                    }
                }
            }
        }
        None
    }

    fn run(ctx: Self::Ctx) {
        let mut rng = rand::thread_rng();
        let mut state = Self::init(&ctx);
        let mut history: Vec<(Self, Option<Self::Event>)> = Vec::new();
        let mut step = 0usize;
        let menu = Self::event_menu();

        loop {
            println!("\n--- Step {} ---", step);
            println!("{}", state);

            // Show the full event menu; the user picks any event and, if it
            // takes inputs, is prompted for each field. We can't cheaply
            // enumerate only-enabled events when inputs range over `nat`.
            println!();
            for (i, spec) in menu.iter().enumerate() {
                if spec.inputs.is_empty() {
                    println!("  {}  {}", i + 1, spec.name);
                } else {
                    let params: Vec<String> = spec
                        .inputs
                        .iter()
                        .map(|p| format!("{}: {}", p.name, p.ty_kind))
                        .collect();
                    println!("  {}  {}({})", i + 1, spec.name, params.join(", "));
                }
            }
            println!();
            println!("  r   Random step");
            println!("  f5  Fast-forward 5 random steps");
            println!("  f10 Fast-forward 10 random steps");
            println!("  f N Fast-forward N random steps");
            println!("  u   Undo");
            println!("  q   Quit");

            print!("\n> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                break;
            }
            let input = input.trim().to_string();
            if input.is_empty() {
                continue;
            }

            match input.as_str() {
                "q" | "quit" => break,
                "u" | "undo" => {
                    if let Some((prev, _)) = history.pop() {
                        state = prev;
                        step = step.saturating_sub(1);
                        println!("Undone.");
                    } else {
                        println!("Nothing to undo.");
                    }
                }
                "r" => {
                    if let Some(evt) = Self::random_enabled_event(&ctx, &state, &mut rng, 32) {
                        let out = Self::output(&ctx, &state, &evt);
                        history.push((state.clone(), Some(evt.clone())));
                        state = Self::action(&ctx, &state, &evt);
                        step += 1;
                        print_fired(&evt, out.as_deref());
                    } else {
                        println!("  No enabled event found.");
                    }
                }
                _ => {
                    // Fast-forward: "f5", "f10", "f 20", "fN"
                    let ff = if input.starts_with('f') {
                        input[1..].trim().parse::<usize>().ok()
                    } else {
                        None
                    };

                    if let Some(n) = ff {
                        let mut stepped = 0;
                        for _ in 0..n {
                            if let Some(evt) =
                                Self::random_enabled_event(&ctx, &state, &mut rng, 32)
                            {
                                let out = Self::output(&ctx, &state, &evt);
                                history.push((state.clone(), Some(evt.clone())));
                                state = Self::action(&ctx, &state, &evt);
                                step += 1;
                                stepped += 1;
                                print_fired(&evt, out.as_deref());
                            } else {
                                println!("  No enabled event after {} steps.", stepped);
                                break;
                            }
                        }
                    } else if let Ok(n) = input.parse::<usize>() {
                        if n >= 1 && n <= menu.len() {
                            let spec = &menu[n - 1];
                            match prompt_inputs_for(spec) {
                                Ok(inputs) => {
                                    match Self::construct_event(spec.name, &inputs) {
                                        Ok(evt) => {
                                            if Self::guard(&ctx, &state, &evt) {
                                                let out = Self::output(&ctx, &state, &evt);
                                                history.push((
                                                    state.clone(),
                                                    Some(evt.clone()),
                                                ));
                                                state = Self::action(&ctx, &state, &evt);
                                                step += 1;
                                                print_fired(&evt, out.as_deref());
                                            } else {
                                                println!(
                                                    "  Guard not satisfied for {}.",
                                                    evt
                                                );
                                            }
                                        }
                                        Err(e) => println!("  {}", e),
                                    }
                                }
                                Err(e) => println!("  {}", e),
                            }
                        } else {
                            println!("Invalid choice.");
                        }
                    } else {
                        println!("Unknown command.");
                    }
                }
            }
        }
    }
}

/// Print a fired event with its output (if any).
fn print_fired<E: fmt::Display>(evt: &E, output: Option<&str>) {
    match output {
        Some(o) => println!("  -> {} = {}", evt, o),
        None => println!("  -> {}", evt),
    }
}

/// Prompt the user for each of an event's input fields, returning the raw
/// strings in order. Bails out on EOF.
fn prompt_inputs_for(spec: &EventSpec) -> Result<Vec<String>, String> {
    let mut out = Vec::with_capacity(spec.inputs.len());
    for input in &spec.inputs {
        print!("    {} ({})? ", input.name, input.ty_kind);
        io::stdout().flush().ok();
        let mut buf = String::new();
        if io::stdin().read_line(&mut buf).is_err() {
            return Err("read error".into());
        }
        out.push(buf.trim().to_string());
    }
    Ok(out)
}

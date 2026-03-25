use rand::seq::SliceRandom;
use std::fmt;
use std::io::{self, Write};

pub trait Animate: Clone + fmt::Display {
    type Ctx;
    type Event: Copy + fmt::Display + fmt::Debug + PartialEq;

    fn init(ctx: &Self::Ctx) -> Self;
    fn events() -> Vec<Self::Event>;
    fn guard(ctx: &Self::Ctx, state: &Self, event: Self::Event) -> bool;
    fn action(ctx: &Self::Ctx, state: &Self, event: Self::Event) -> Self;

    fn enabled_events(ctx: &Self::Ctx, state: &Self) -> Vec<Self::Event> {
        Self::events()
            .into_iter()
            .filter(|e| Self::guard(ctx, state, *e))
            .collect()
    }

    fn run(ctx: Self::Ctx) {
        let mut rng = rand::thread_rng();
        let mut state = Self::init(&ctx);
        let mut history: Vec<(Self, Option<Self::Event>)> = Vec::new();
        let mut step = 0usize;

        loop {
            println!("\n--- Step {} ---", step);
            println!("{}", state);

            let enabled = Self::enabled_events(&ctx, &state);
            if enabled.is_empty() {
                println!("\nDEADLOCK: no events enabled.");
                if history.is_empty() {
                    break;
                }
                println!("  u  Undo");
                println!("  q  Quit");
            } else {
                println!();
                for (i, e) in enabled.iter().enumerate() {
                    println!("  {}  {}", i + 1, e);
                }
                println!();
                println!("  r   Random step");
                println!("  f5  Fast-forward 5 random steps");
                println!("  f10 Fast-forward 10 random steps");
                println!("  f N Fast-forward N random steps");
                println!("  u   Undo");
                println!("  q   Quit");
            }

            print!("\n> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                break;
            }
            let input = input.trim();
            if input.is_empty() {
                continue;
            }

            match input {
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
                    let enabled = Self::enabled_events(&ctx, &state);
                    if let Some(&evt) = enabled.choose(&mut rng) {
                        history.push((state.clone(), Some(evt)));
                        state = Self::action(&ctx, &state, evt);
                        step += 1;
                        println!("  -> {}", evt);
                    }
                }
                _ => {
                    // Fast-forward: "f5", "f10", "f 20", "f N"
                    let ff = if input.starts_with('f') {
                        input[1..].trim().parse::<usize>().ok()
                    } else {
                        None
                    };

                    if let Some(n) = ff {
                        for _ in 0..n {
                            let enabled = Self::enabled_events(&ctx, &state);
                            if let Some(&evt) = enabled.choose(&mut rng) {
                                history.push((state.clone(), Some(evt)));
                                state = Self::action(&ctx, &state, evt);
                                step += 1;
                                println!("  -> {}", evt);
                            } else {
                                println!("  DEADLOCK after {} steps.", step);
                                break;
                            }
                        }
                    } else if let Ok(n) = input.parse::<usize>() {
                        let enabled = Self::enabled_events(&ctx, &state);
                        if n >= 1 && n <= enabled.len() {
                            let evt = enabled[n - 1];
                            history.push((state.clone(), Some(evt)));
                            state = Self::action(&ctx, &state, evt);
                            step += 1;
                            println!("  -> {}", evt);
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

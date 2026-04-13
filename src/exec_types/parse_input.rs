//! `ParseInput` — convert a user-typed string into a concrete input value.
//!
//! Used by generated `construct_event` impls to parse one field at a time
//! from an input prompt. Distinct from `FromStr` only so the generated code
//! can speak one trait name regardless of the input type, and so error
//! messages can be shaped uniformly.

use super::nat::Nat;

pub trait ParseInput: Sized {
    fn parse_input(s: &str) -> Result<Self, String>;
}

impl ParseInput for () {
    fn parse_input(_: &str) -> Result<Self, String> {
        Ok(())
    }
}

impl ParseInput for Nat {
    fn parse_input(s: &str) -> Result<Self, String> {
        s.trim().parse()
    }
}

impl ParseInput for bool {
    fn parse_input(s: &str) -> Result<Self, String> {
        match s.trim() {
            "t" | "true" | "1" | "y" | "yes" => Ok(true),
            "f" | "false" | "0" | "n" | "no" => Ok(false),
            other => Err(format!("could not parse {:?} as bool", other)),
        }
    }
}

macro_rules! impl_parse_int {
    ($($t:ty),*) => {
        $(
            impl ParseInput for $t {
                fn parse_input(s: &str) -> Result<Self, String> {
                    s.trim().parse::<$t>().map_err(|e| e.to_string())
                }
            }
        )*
    };
}
impl_parse_int!(i32, i64, u32, u64, usize, isize);

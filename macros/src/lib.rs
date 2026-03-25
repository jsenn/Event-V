extern crate proc_macro;

mod animate;
mod expand;
mod parse;

use proc_macro::TokenStream;
use quote::quote;

/// Proc macro for defining Verus state machines with a concise DSL.
///
/// Generates:
/// - All spec/proof trait implementations (wrapped in `verus! { }`)
/// - An `animate` module with executable state/event types for simulation
///
/// # Example
///
/// ```ignore
/// verus_machine! {
///     deadlock_free machine Abs {
///         ctx: BridgeCtx,
///
///         state {
///             cars: nat,
///         }
///
///         init(ctx) {
///             cars: 0
///         }
///
///         invariant(ctx, state) {
///             state.cars <= ctx.max_cars
///         }
///
///         event MainlandIn {
///             guard(ctx, state) {
///                 state.cars > 0
///             }
///             action(ctx, state) {
///                 Abs { cars: (state.cars - 1) as nat, ..state }
///             }
///         }
///     }
/// }
/// ```
#[proc_macro]
pub fn verus_machine(input: TokenStream) -> TokenStream {
    let decl = syn::parse_macro_input!(input as parse::MachineDecl);
    let spec = expand::expand_spec(&decl);
    let anim = animate::expand_animate(&decl);
    let output = quote! {
        #spec
        #anim
    };
    output.into()
}

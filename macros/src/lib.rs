extern crate proc_macro;

mod expand;
mod parse;

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn verus_machine(input: TokenStream) -> TokenStream {
    let macro_input = syn::parse_macro_input!(input as parse::MacroInput);

    let machine_code = macro_input.machine.as_ref().map(|decl| {
        let spec = expand::expand_spec(decl);
        quote! { #spec }
    });

    let output = quote! {
        #machine_code
    };
    output.into()
}

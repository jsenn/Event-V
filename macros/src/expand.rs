use proc_macro2::TokenStream;
use quote::quote;
use syn::Path;

use crate::parse::*;

/// Given a refines path like `abs::Abs`, replace the last segment with `event_name`
/// to produce `abs::MainlandIn` etc.
fn abstract_event_path(refines_path: &Path, event_name: &syn::Ident) -> TokenStream {
    let mut path = refines_path.clone();
    if let Some(last) = path.segments.last_mut() {
        last.ident = event_name.clone();
        last.arguments = syn::PathArguments::None;
    }
    quote! { #path }
}

pub fn expand_spec(decl: &MachineDecl) -> TokenStream {
    let name = &decl.name;
    let ctx_type = decl.ctx.spec_type();

    // --- State struct ---
    let field_defs: Vec<_> = decl
        .state_fields
        .iter()
        .map(|f| {
            let fname = &f.name;
            let fty = &f.ty;
            quote! { pub #fname: #fty }
        })
        .collect();

    // --- validate method + Machine impl ---
    let init_ctx = &decl.init.ctx_name;
    let init_body = &decl.init.body;

    // Generate validate method on the struct.
    // Abstract machines: validate = user invariant body
    // Refined machines: validate = abstract_validate && user invariant body
    let validate_impl = if let Some(ref inv) = decl.invariant {
        let inv_ctx = &inv.ctx_name;
        let inv_state = &inv.state_name;
        let inv_body = &inv.body;

        if decl.refines.is_some() {
            quote! {
                impl #name {
                    pub open spec fn validate(&self, #inv_ctx: #ctx_type) -> bool {
                        let #inv_state = *self;
                        self.lift().validate(#inv_ctx) && { #inv_body }
                    }
                }
            }
        } else {
            quote! {
                impl #name {
                    pub open spec fn validate(&self, #inv_ctx: #ctx_type) -> bool {
                        let #inv_state = *self;
                        #inv_body
                    }
                }
            }
        }
    } else if decl.refines.is_some() {
        // No user invariant but machine refines — just check abstract
        quote! {
            impl #name {
                pub open spec fn validate(&self, ctx: #ctx_type) -> bool {
                    self.lift().validate(ctx)
                }
            }
        }
    } else {
        // No invariant, no refinement — trivially true
        quote! {
            impl #name {
                pub open spec fn validate(&self, _ctx: #ctx_type) -> bool {
                    true
                }
            }
        }
    };

    let machine_impl = quote! {
        impl Machine for #name {
            type Ctx = #ctx_type;

            open spec fn init(#init_ctx: Self::Ctx) -> Self {
                #name {
                    #init_body
                }
            }

            open spec fn inv(ctx: Self::Ctx, state: Self) -> bool {
                state.validate(ctx)
            }

            proof fn proof_init_safety(ctx: Self::Ctx) {}
        }
    };

    // --- Lift impl (refinements only) ---
    let lift_impl = if let (Some(ref refines_path), Some(ref lift_decl)) =
        (&decl.refines, &decl.lift)
    {
        let lift_state = &lift_decl.state_name;
        let lift_body = &lift_decl.body;
        quote! {
            impl Lift<#refines_path> for #name {
                open spec fn lift(&self) -> #refines_path {
                    let #lift_state = *self;
                    #lift_body
                }
            }
        }
    } else {
        quote! {}
    };

    // --- Refinement impl ---
    let refinement_impl = if let Some(ref refines_path) = decl.refines {
        quote! {
            impl Refinement for #name {
                type Abstract = #refines_path;

                open spec fn lift_ctx(ctx: Self::Ctx) -> <Self::Abstract as Machine>::Ctx {
                    ctx
                }

                proof fn proof_lift_ctx_valid(ctx: Self::Ctx) {}
                proof fn proof_init_lift(ctx: Self::Ctx) {}
                proof fn proof_lift_safe(ctx: Self::Ctx, state: Self) {}
            }
        }
    } else {
        quote! {}
    };

    // --- Event impls ---
    let event_impls: Vec<_> = decl.events.iter().map(|evt| expand_event(decl, evt)).collect();

    // --- Deadlock freedom proof ---
    // Use standard || infix instead of ||| prefix (quote! tokens lack real
    // span/line info, which Verus needs to parse ||| prefix operators).
    let deadlock_proof = if decl.deadlock_free {
        let guards: Vec<_> = decl
            .events
            .iter()
            .map(|evt| {
                let ename = &evt.name;
                quote! { #ename::guard(ctx, state) }
            })
            .collect();

        let guard_disjunction = if guards.len() == 1 {
            guards[0].clone()
        } else {
            let first = &guards[0];
            let rest = &guards[1..];
            quote! { #first #(|| #rest)* }
        };

        quote! {
            proof fn proof_deadlock_free(ctx: #ctx_type, state: #name)
                requires
                    ctx.valid(),
                    #name::inv(ctx, state),
                ensures
                    #guard_disjunction,
            {}
        }
    } else {
        quote! {}
    };

    // --- Auxiliary functions ---
    let aux_fn_impls: Vec<_> = decl
        .aux_fns
        .iter()
        .map(|f| {
            let fn_name = &f.name;
            let state_name = &f.state_name;
            let ret_type = &f.ret_type;
            let body = &f.body;
            quote! {
                pub open spec fn #fn_name(&self) -> #ret_type {
                    let #state_name = *self;
                    #body
                }
            }
        })
        .collect();

    let aux_fns_impl = if aux_fn_impls.is_empty() {
        quote! {}
    } else {
        quote! {
            impl #name {
                #(#aux_fn_impls)*
            }
        }
    };

    // --- Inline ctx struct + MachineContext impl ---
    let ctx_struct_impl = match &decl.ctx {
        CtxDecl::Inline { fields, valid } => {
            let ctx_field_defs: Vec<_> = fields
                .iter()
                .map(|f| {
                    let fname = &f.name;
                    let fty = &f.ty;
                    quote! { pub #fname: #fty }
                })
                .collect();

            let valid_impl = if let Some(v) = valid {
                let v_ctx = &v.ctx_name;
                let v_body = &v.body;
                quote! {
                    impl MachineContext for Ctx {
                        open spec fn valid(&self) -> bool {
                            let #v_ctx = *self;
                            #v_body
                        }
                    }
                }
            } else {
                quote! {
                    impl MachineContext for Ctx {
                        open spec fn valid(&self) -> bool {
                            true
                        }
                    }
                }
            };

            quote! {
                pub struct Ctx {
                    #(#ctx_field_defs,)*
                }

                #valid_impl
            }
        }
        CtxDecl::External(_) => quote! {},
    };

    // --- Wrap everything in verus! ---
    quote! {
        verus! {
            #ctx_struct_impl

            pub struct #name {
                #(#field_defs,)*
            }

            #aux_fns_impl

            #validate_impl

            #lift_impl

            #machine_impl

            #refinement_impl

            #(#event_impls)*

            #deadlock_proof
        }
    }
}

fn expand_event(decl: &MachineDecl, evt: &EventDecl) -> TokenStream {
    let machine_name = &decl.name;
    let ctx_type = decl.ctx.spec_type();
    let event_name = &evt.name;

    let guard_ctx = &evt.guard.ctx_name;
    let guard_state = &evt.guard.state_name;
    let guard_body = &evt.guard.body;

    let action_ctx = &evt.action.ctx_name;
    let action_state = &evt.action.state_name;
    let action_body = &evt.action.body;

    let event_struct = quote! {
        pub struct #event_name;
    };

    let event_impl = quote! {
        impl Event<#machine_name> for #event_name {
            open spec fn guard(#guard_ctx: #ctx_type, #guard_state: #machine_name) -> bool {
                #guard_body
            }

            open spec fn action(#action_ctx: #ctx_type, #action_state: #machine_name) -> #machine_name {
                #action_body
            }

            proof fn proof_safety(ctx: #ctx_type, state: #machine_name) {}
        }
    };

    let refined_impl = if evt.refined {
        if let Some(ref refines_path) = decl.refines {
            let abstract_event = abstract_event_path(refines_path, event_name);
            quote! {
                impl RefinedEvent<#machine_name, #abstract_event> for #event_name {
                    proof fn proof_strengthening(ctx: #ctx_type, state: #machine_name) {}
                    proof fn proof_simulation(ctx: #ctx_type, state: #machine_name) {}
                }
            }
        } else {
            quote! { compile_error!("'refined' event used but machine does not 'refines' anything"); }
        }
    } else {
        quote! {}
    };

    let convergent_impl = if evt.convergent {
        if let Some(ref var) = evt.variant {
            let var_ctx = &var.ctx_name;
            let var_state = &var.state_name;
            let var_body = &var.body;
            quote! {
                impl ConvergentEvent<#machine_name> for #event_name {
                    open spec fn variant(#var_ctx: #ctx_type, #var_state: #machine_name) -> nat {
                        #var_body
                    }
                    proof fn proof_convergence(ctx: #ctx_type, state: #machine_name) {}
                }
            }
        } else {
            quote! { compile_error!("'convergent' event requires a 'variant' block"); }
        }
    } else {
        quote! {}
    };

    let new_impl = if evt.concrete {
        quote! {
            impl NewEvent<#machine_name> for #event_name {
                proof fn proof_stuttering(ctx: #ctx_type, state: #machine_name) {}
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #event_struct
        #event_impl
        #refined_impl
        #convergent_impl
        #new_impl
    }
}

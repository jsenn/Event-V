use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
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

    if decl.refines.is_none() {
        if let Some(evt) = decl.events.iter().find(|e| e.concrete) {
            return syn::Error::new(
                evt.name.span(),
                "'concrete' events may only appear in a machine that 'refines' another \
                 (a concrete event is one introduced by a refinement that has no abstract counterpart); \
                 either remove 'concrete' or add 'refines <abstract>' to the machine header",
            )
            .to_compile_error();
        }
    }

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

    // --- validate method ---
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
        quote! {
            impl #name {
                pub open spec fn validate(&self, ctx: #ctx_type) -> bool {
                    self.lift().validate(ctx)
                }
            }
        }
    } else {
        quote! {
            impl #name {
                pub open spec fn validate(&self, _ctx: #ctx_type) -> bool {
                    true
                }
            }
        }
    };

    // --- Machine impl (no longer contains init) ---
    let machine_impl = quote! {
        impl Machine for #name {
            type Context = #ctx_type;

            open spec fn inv(ctx: Self::Context, state: Self) -> bool {
                state.validate(ctx)
            }
        }
    };

    // --- Init impl ---
    let init_ctx = &decl.init.ctx_name;
    let init_body = &decl.init.body;
    let init_span = init_ctx.span();
    let init_impl = quote_spanned! { init_span =>
        pub struct Initialize;

        impl Init<#name> for Initialize {
            type Input = ();

            open spec fn init(#init_ctx: #ctx_type, _input: ()) -> #name {
                #name {
                    #init_body
                }
            }

            proof fn proof_safety(ctx: #ctx_type, _input: ()) {}
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
        let abstract_init = abstract_event_path(refines_path, &syn::Ident::new("Initialize", name.span()));
        let has_concrete_event = decl.events.iter().any(|e| e.concrete);
        let convergent_impl = match (&decl.variant, has_concrete_event) {
            (Some(v), _) => {
                let v_ctx = &v.ctx_name;
                let v_state = &v.state_name;
                let v_ty = &v.ret_type;
                let v_body = &v.body;
                quote! {
                    impl ConvergentRefinement for #name {
                        type Variant = #v_ty;

                        open spec fn variant(#v_ctx: Self::Context, #v_state: Self) -> Self::Variant {
                            #v_body
                        }
                    }
                }
            }
            (None, true) => {
                let err = syn::Error::new(
                    name.span(),
                    "machine with 'concrete' events must declare a machine-level 'variant(ctx, state) -> Type { ... }' block",
                );
                return err.to_compile_error();
            }
            (None, false) => quote! {},
        };
        quote! {
            impl Refinement for #name {
                type Abstract = #refines_path;

                open spec fn lift_ctx(ctx: Self::Context) -> <Self::Abstract as Machine>::Context {
                    ctx
                }

                proof fn proof_lift_ctx_valid(ctx: Self::Context) {}
                proof fn proof_lift_safe(ctx: Self::Context, state: Self) {}
            }

            #convergent_impl

            impl RefinedInit<#name, #abstract_init> for Initialize {
                open spec fn lift_in(_input: ()) -> () { () }

                proof fn proof_simulation(ctx: #ctx_type, _input: ()) {}
            }
        }
    } else {
        quote! {}
    };

    // --- Event impls ---
    let event_impls: Vec<_> = decl.events.iter().map(|evt| expand_event(decl, evt)).collect();

    // --- Deadlock freedom proof ---
    // For events with non-() Input, witness the existential via `exists|x: T| guard(..., x)`.
    // For () Input, call the guard directly (Verus's auto-witness of `()` in an existential
    // is unreliable).
    let deadlock_proof = if decl.deadlock_free {
        if decl.events.is_empty() {
            syn::Error::new(
                name.span(),
                "'deadlock_free' machine must declare at least one event \
                 (a machine with no events is trivially deadlocked)",
            )
            .to_compile_error()
        } else {
            let guards: Vec<_> = decl
                .events
                .iter()
                .map(|evt| {
                    let ename = &evt.name;
                    if let Some(ref param) = evt.input {
                        let pname = &param.name;
                        let pty = &param.ty;
                        // Explicit #[trigger] on the guard call: needed because
                        // `Event::guard` is `open spec`, so after unfolding the
                        // bound variable typically only appears inside raw
                        // arithmetic / built-ins that Verus rejects as triggers.
                        // Keeping `Event::guard(...)` as the trigger pattern
                        // preserves a well-formed quantifier regardless of body.
                        quote! { exists|#pname: #pty| #[trigger] #ename::guard(ctx, state, #pname) }
                    } else {
                        quote! { #ename::guard(ctx, state, ()) }
                    }
                })
                .collect();

            let guard_disjunction = if guards.len() == 1 {
                guards[0].clone()
            } else {
                let first = &guards[0];
                let rest = &guards[1..];
                quote! { #first #(|| #rest)* }
            };

            let dl_span = name.span();
            quote_spanned! { dl_span =>
                proof fn proof_deadlock_free(ctx: #ctx_type, state: #name)
                    requires
                        ctx.valid(),
                        #name::inv(ctx, state),
                    ensures
                        #guard_disjunction,
                {}
            }
        }
    } else {
        quote! {}
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

            #validate_impl

            #lift_impl

            #machine_impl

            #init_impl

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

    // --- Input type and parameter tokens ---
    // When the event has an input (e.g. `event Put(elem: nat)`), the user-chosen
    // param name is used as the formal parameter so it's visible inside
    // guard/action/output bodies.
    let (input_type, input_param) = if let Some(ref param) = evt.input {
        let ty = &param.ty;
        let name = &param.name;
        (quote! { #ty }, quote! { #name: #ty })
    } else {
        (quote! { () }, quote! { _input: () })
    };

    // --- Output type ---
    let output_type = if let Some(ref ty) = evt.output_type {
        quote! { #ty }
    } else {
        quote! { () }
    };

    // --- Output function body ---
    let output_fn = if let Some(ref output) = evt.output {
        let out_ctx = &output.ctx_name;
        let out_state = &output.state_name;
        let out_body = &output.body;
        quote! {
            open spec fn output(#out_ctx: #ctx_type, #out_state: #machine_name, #input_param) -> #output_type {
                #out_body
            }
        }
    } else {
        // No user-provided output block — emit a trivial `()` output.
        quote! {
            open spec fn output(_ctx: #ctx_type, _state: #machine_name, _input: #input_type) -> () {
                ()
            }
        }
    };

    let event_struct = quote! {
        pub struct #event_name;
    };

    let (safety_span, safety_body) = match &evt.safety_proof {
        Some(p) => (p.span, { let b = &p.body; quote! { #b } }),
        None => (event_name.span(), quote! {}),
    };
    let event_impl = quote_spanned! { safety_span =>
        impl Event<#machine_name> for #event_name {
            type Input = #input_type;
            type Output = #output_type;

            open spec fn guard(#guard_ctx: #ctx_type, #guard_state: #machine_name, #input_param) -> bool {
                #guard_body
            }

            open spec fn action(#action_ctx: #ctx_type, #action_state: #machine_name, #input_param) -> #machine_name {
                #action_body
            }

            #output_fn

            proof fn proof_safety(ctx: #ctx_type, state: #machine_name, #input_param) {
                #safety_body
            }
        }
    };

    let refined_impl = if evt.refined {
        if let Some(ref refines_path) = decl.refines {
            let abstract_event = abstract_event_path(refines_path, event_name);

            // lift_in: map concrete input to abstract input.
            let lift_in_fn = if let Some(ref li) = evt.lift_in {
                let li_param = &li.param_name;
                let li_body = &li.body;
                quote! {
                    open spec fn lift_in(#li_param: #input_type)
                        -> <#abstract_event as Event<#refines_path>>::Input
                    {
                        #li_body
                    }
                }
            } else {
                // Default: map to unit. Works when the abstract input type is `()`.
                quote! {
                    open spec fn lift_in(_input: #input_type)
                        -> <#abstract_event as Event<#refines_path>>::Input
                    {
                        ()
                    }
                }
            };

            // lift_out: map concrete output to abstract output.
            let lift_out_fn = if let Some(ref lo) = evt.lift_out {
                let lo_param = &lo.param_name;
                let lo_body = &lo.body;
                quote! {
                    open spec fn lift_out(#lo_param: #output_type)
                        -> <#abstract_event as Event<#refines_path>>::Output
                    {
                        #lo_body
                    }
                }
            } else {
                quote! {
                    open spec fn lift_out(_output: #output_type)
                        -> <#abstract_event as Event<#refines_path>>::Output
                    {
                        ()
                    }
                }
            };

            let (_str_span, str_body) = match &evt.strengthening_proof {
                Some(p) => (p.span, { let b = &p.body; quote! { #b } }),
                None => (event_name.span(), quote! {}),
            };
            let (_sim_span, sim_body) = match &evt.simulation_proof {
                Some(p) => (p.span, { let b = &p.body; quote! { #b } }),
                None => (event_name.span(), quote! {}),
            };
            let refined_span = evt.strengthening_proof.as_ref()
                .or(evt.simulation_proof.as_ref())
                .map(|p| p.span)
                .unwrap_or_else(|| event_name.span());
            quote_spanned! { refined_span =>
                impl RefinedEvent<#machine_name, #abstract_event> for #event_name {
                    #lift_in_fn
                    #lift_out_fn

                    proof fn proof_strengthening(ctx: #ctx_type, state: #machine_name, #input_param) {
                        #str_body
                    }
                    proof fn proof_simulation(ctx: #ctx_type, state: #machine_name, #input_param) {
                        #sim_body
                    }
                }
            }
        } else {
            quote! { compile_error!("'refined' event used but machine does not 'refines' anything"); }
        }
    } else {
        quote! {}
    };

    let new_impl = if evt.concrete {
        let (stut_span, stut_body) = match &evt.stuttering_proof {
            Some(p) => (p.span, { let b = &p.body; quote! { #b } }),
            None => (event_name.span(), quote! {}),
        };
        let (conv_span, conv_body) = match &evt.convergence_proof {
            Some(p) => (p.span, { let b = &p.body; quote! { #b } }),
            None => (event_name.span(), quote! {}),
        };
        let conv_method = quote_spanned! { conv_span =>
            proof fn proof_convergent(ctx: #ctx_type, state: #machine_name, #input_param) {
                #conv_body
            }
        };
        let stut_method = quote_spanned! { stut_span =>
            proof fn proof_stuttering(ctx: #ctx_type, state: #machine_name, #input_param) {
                #stut_body
            }
        };
        quote! {
            impl NewEvent<#machine_name> for #event_name {
                #conv_method
                #stut_method
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #event_struct
        #event_impl
        #refined_impl
        #new_impl
    }
}

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use verus_syn::{Error, Ident, Path, PathArguments};

use crate::parse::*;

/// Given a refines path like `abs::Abs`, replace the last segment with `event_name`
/// to produce `abs::MainlandIn` etc.
fn abstract_event_path(refines_path: &Path, event_name: &Ident) -> TokenStream {
    let mut path = refines_path.clone();
    if let Some(last) = path.segments.last_mut() {
        last.ident = event_name.clone();
        last.arguments = PathArguments::None;
    }
    quote! { #path }
}

fn typed_param(p: &ClosureParam, fallback: impl ToTokens) -> TokenStream {
    let name = &p.name;
    match &p.ty {
        Some(ty) => quote! { #name: #ty },
        None => quote! { #name: #fallback },
    }
}

fn let_param(p: &ClosureParam) -> TokenStream {
    let name = &p.name;
    match &p.ty {
        Some(ty) => quote! { #name: #ty },
        None => quote! { #name },
    }
}

pub fn expand_spec(decl: &MachineDecl) -> TokenStream {
    let name = &decl.name;
    let context_type = decl.context.spec_type();

    if decl.refines.is_none() {
        if let Some(evt) = decl.events.iter().find(|e| e.concrete) {
            return Error::new(
                evt.name.span(),
                "'concrete' events may only appear in a machine that 'refines' another \
                 (a concrete event is one introduced by a refinement that has no abstract counterpart); \
                 either remove 'concrete' or add 'refines <abstract>' to the machine header",
            )
            .to_compile_error();
        }
        if let Some(lc) = &decl.lift_context {
            return Error::new(
                lc.context.name.span(),
                "'lift_context' may only appear in a machine that 'refines' another",
            )
            .to_compile_error();
        }
        if let Some(p) = &decl.proof_lift_context_valid {
            return Error::new(
                p.context.name.span(),
                "'proof_lift_context_valid' may only appear in a machine that 'refines' another",
            )
            .to_compile_error();
        }
        if let Some(p) = &decl.proof_lift_safe {
            return Error::new(
                p.span,
                "'proof_lift_safe' may only appear in a machine that 'refines' another",
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
    // Refined machines: validate = abstract_validate(lifted context) && user invariant body
    //
    // The context lift is `<Self as Lift<ConcreteContext, AbstractContext>>::lift` — written fully
    // qualified because the machine carries two `Lift` impls (state and context).
    let lifted_context = |context_ident: &Ident| -> TokenStream {
        match &decl.refines {
            Some(refines_path) => quote! {
                <#name as Lift<#context_type, <#refines_path as Machine>::Context>>::lift(#context_ident)
            },
            None => quote! { #context_ident },
        }
    };

    let validate_impl = if let Some(ref inv) = decl.invariant {
        let inv_context_sig = typed_param(&inv.context, &context_type);
        let inv_state_let = let_param(&inv.state);
        let inv_body = &inv.body;

        if decl.refines.is_some() {
            let lifted = lifted_context(&inv.context.name);
            quote! {
                impl #name {
                    pub open spec fn validate(&self, #inv_context_sig) -> bool {
                        let #inv_state_let = *self;
                        self.lift().validate(#lifted) && { #inv_body }
                    }
                }
            }
        } else {
            quote! {
                impl #name {
                    pub open spec fn validate(&self, #inv_context_sig) -> bool {
                        let #inv_state_let = *self;
                        #inv_body
                    }
                }
            }
        }
    } else if decl.refines.is_some() {
        let context_ident = Ident::new("context", name.span());
        let lifted = lifted_context(&context_ident);
        quote! {
            impl #name {
                pub open spec fn validate(&self, context: #context_type) -> bool {
                    self.lift().validate(#lifted)
                }
            }
        }
    } else {
        quote! {
            impl #name {
                pub open spec fn validate(&self, _context: #context_type) -> bool {
                    true
                }
            }
        }
    };

    // --- Machine impl (no longer contains init) ---
    let machine_impl = quote! {
        impl Machine for #name {
            type Context = #context_type;

            open spec fn invariant(context: Self::Context, state: Self) -> bool {
                state.validate(context)
            }
        }
    };

    // --- Init impl ---
    let init_context_sig = typed_param(&decl.init.context, &context_type);
    let init_body = &decl.init.body;
    let init_span = decl.init.context.name.span();
    let init_impl = quote_spanned! { init_span =>
        #[allow(dead_code)]
        pub struct Initialize;

        impl Init<#name> for Initialize {
            type Input = ();

            open spec fn init(#init_context_sig, _input: ()) -> #name {
                #init_body
            }

            proof fn proof_safety(_context: #context_type, _input: ()) {}
        }
    };

    // --- Lift impls (refinements only): state lift + context lift, keyed on the machine ---
    let lift_impl = if let Some(ref refines_path) = decl.refines {
        let lift_decl = match &decl.lift {
            Some(l) => l,
            None => {
                return Error::new(
                    name.span(),
                    "a machine that 'refines' another must declare a 'lift: |state| ...' block",
                )
                .to_compile_error();
            }
        };
        let lift_state_sig = typed_param(&lift_decl.state, name);
        let lift_body = &lift_decl.body;

        let (lc_context_sig, lc_body) = match &decl.lift_context {
            Some(lc) => (typed_param(&lc.context, &context_type), lc.body.clone()),
            None => (
                quote! { context: #context_type },
                quote! { context },
            ),
        };

        // `&self` convenience for the context lift — only for an inline `context { }` declaration,
        // whose `Context` struct is unique to this machine. An external context type may be shared
        // between machines, so an inherent `lift` method on it would collide.
        let context_helper = match &decl.context {
            ContextDecl::Inline { .. } => quote! {
                impl #context_type {
                    pub open spec fn lift(&self) -> <#refines_path as Machine>::Context {
                        <#name as Lift<#context_type, <#refines_path as Machine>::Context>>::lift(*self)
                    }
                }
            },
            ContextDecl::External(_) => quote! {},
        };

        quote! {
            impl Lift<#name, #refines_path> for #name {
                open spec fn lift(#lift_state_sig) -> #refines_path {
                    #lift_body
                }
            }

            impl Lift<#context_type, <#refines_path as Machine>::Context> for #name {
                open spec fn lift(#lc_context_sig) -> <#refines_path as Machine>::Context {
                    #lc_body
                }
            }

            impl #name {
                pub open spec fn lift(&self) -> #refines_path {
                    <#name as Lift<#name, #refines_path>>::lift(*self)
                }

                pub open spec fn lift_context(context: #context_type)
                    -> <#refines_path as Machine>::Context
                {
                    <#name as Lift<#context_type, <#refines_path as Machine>::Context>>::lift(context)
                }
            }

            #context_helper
        }
    } else {
        quote! {}
    };

    // --- Refinement impl ---
    let refinement_impl = if let Some(ref refines_path) = decl.refines {
        let abstract_init = abstract_event_path(refines_path, &Ident::new("Initialize", name.span()));
        let has_concrete_event = decl.events.iter().any(|e| e.concrete);
        let convergent_impl = match (&decl.variant, has_concrete_event) {
            (Some(v), _) => {
                let v_context_sig = typed_param(&v.context, quote! { Self::Context });
                let v_state_sig = typed_param(&v.state, quote! { Self });
                let v_ty = &v.ret_type;
                let v_body = &v.body;
                quote! {
                    impl ConvergentRefinement for #name {
                        type Variant = #v_ty;

                        open spec fn variant(#v_context_sig, #v_state_sig) -> Self::Variant {
                            #v_body
                        }
                    }
                }
            }
            (None, true) => {
                let err = Error::new(
                    name.span(),
                    "machine with 'concrete' events must declare a machine-level 'variant: |context, state| -> Type { ... }' block",
                );
                return err.to_compile_error();
            }
            (None, false) => quote! {},
        };

        let proof_lift_context_valid_fn = match &decl.proof_lift_context_valid {
            Some(p) => {
                let p_context_sig = typed_param(&p.context, &context_type);
                let p_body = &p.body;
                quote! {
                    proof fn proof_lift_context_valid(#p_context_sig) {
                        #p_body
                    }
                }
            }
            None => quote! {
                proof fn proof_lift_context_valid(_context: #context_type) {}
            },
        };

        let proof_lift_safe_fn = match &decl.proof_lift_safe {
            Some(p) => {
                let p_context_sig = typed_param(&p.context, &context_type);
                let p_state_sig = typed_param(&p.state, quote! { Self });
                let p_body = &p.body;
                quote_spanned! { p.span =>
                    proof fn proof_lift_safe(#p_context_sig, #p_state_sig) {
                        #p_body
                    }
                }
            }
            None => quote! {
                proof fn proof_lift_safe(_context: #context_type, _state: Self) {}
            },
        };

        quote! {
            impl Refinement for #name {
                type Abstract = #refines_path;

                #proof_lift_context_valid_fn

                #proof_lift_safe_fn
            }

            #convergent_impl

            impl RefinedInit<#name, #abstract_init> for Initialize {
                open spec fn lift_in(_input: ()) -> () { () }

                proof fn proof_simulation(_context: #context_type, _input: ()) {}
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
    let deadlock_proof = if let Some(dl_span) = decl.deadlock_free {
        if decl.events.is_empty() {
            Error::new(
                dl_span,
                "'deadlock_free' machine must declare at least one event \
                 (a machine with no events is trivially deadlocked)",
            )
            .to_compile_error()
        } else {
            // The context/state parameter names are fixed for the auto-generated
            // proof, but taken from the closure for a user-supplied one.
            let (ctx, state_ident, ctx_sig, state_sig) = match &decl.proof_deadlock_free {
                Some(p) => (
                    p.context.name.clone(),
                    p.state.name.clone(),
                    typed_param(&p.context, &context_type),
                    typed_param(&p.state, name),
                ),
                None => {
                    let ctx = Ident::new("context", dl_span);
                    let state_ident = Ident::new("state", dl_span);
                    let ctx_sig = quote! { #ctx: #context_type };
                    let state_sig = quote! { #state_ident: #name };
                    (ctx, state_ident, ctx_sig, state_sig)
                }
            };

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
                        quote! { exists|#pname: #pty| #[trigger] #ename::guard(#ctx, #state_ident, #pname) }
                    } else {
                        quote! { #ename::guard(#ctx, #state_ident, ()) }
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

            let proof_signature = quote! {
                proof fn proof_deadlock_free(#ctx_sig, #state_sig)
                    requires
                        #ctx.valid(),
                        #name::invariant(#ctx, #state_ident),
                    ensures
                        #guard_disjunction,
            };

            match &decl.proof_deadlock_free {
                Some(p) => {
                    let body = &p.body;
                    quote_spanned! { dl_span =>
                        #proof_signature
                        {
                            #body
                        }
                    }
                }
                None => {
                    // No user proof: route the obligation through a helper whose
                    // `custom_err` reproduces the disjunction as a ready-to-paste
                    // `proof_deadlock_free` block, so a failure is actionable.
                    let disjuncts: Vec<String> = decl
                        .events
                        .iter()
                        .map(|evt| {
                            let ename = &evt.name;
                            match &evt.input {
                                Some(param) => {
                                    let pname = &param.name;
                                    let pty = param.ty.to_token_stream().to_string();
                                    format!("exists|{pname}: {pty}| #[trigger] {ename}::guard(context, state, {pname})")
                                }
                                None => format!("{ename}::guard(context, state, ())"),
                            }
                        })
                        .collect();
                    let msg = format!(
                        "machine `{}` is declared `deadlock_free`, but Verus could not \
                         prove it automatically -- it may deadlock. To debug, paste this \
                         into the machine and refine it with `assert`: \
                         proof_deadlock_free: |context, state| {{ assert({}); }}",
                        name,
                        disjuncts.join(" || "),
                    );
                    quote_spanned! { dl_span =>
                        proof fn deadlock_obligation(b: bool)
                            requires
                                #![verifier::custom_err(#msg)]
                                b,
                            ensures
                                b,
                        {
                        }

                        #proof_signature
                        {
                            deadlock_obligation(#guard_disjunction);
                        }
                    }
                }
            }
        }
    } else {
        if let Some(p) = &decl.proof_deadlock_free {
            return Error::new(
                p.span,
                "'proof_deadlock_free' may only appear in a 'deadlock_free' machine",
            )
            .to_compile_error();
        }
        quote! {}
    };

    // --- Inline context struct + MachineContext impl ---
    let context_struct_impl = match &decl.context {
        ContextDecl::Inline { fields, valid } => {
            let context_field_defs: Vec<_> = fields
                .iter()
                .map(|f| {
                    let fname = &f.name;
                    let fty = &f.ty;
                    quote! { pub #fname: #fty }
                })
                .collect();

            let valid_impl = if let Some(v) = valid {
                let v_context_let = let_param(&v.context);
                let v_body = &v.body;
                quote! {
                    impl MachineContext for Context {
                        open spec fn valid(&self) -> bool {
                            let #v_context_let = *self;
                            #v_body
                        }
                    }
                }
            } else {
                quote! {
                    impl MachineContext for Context {
                        open spec fn valid(&self) -> bool {
                            true
                        }
                    }
                }
            };

            quote! {
                pub struct Context {
                    #(#context_field_defs,)*
                }

                #valid_impl
            }
        }
        ContextDecl::External(_) => quote! {},
    };

    // --- Wrap everything in verus! ---
    quote! {
        verus! {
            #context_struct_impl

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
    let context_type = decl.context.spec_type();
    let event_name = &evt.name;

    let guard_context = typed_param(&evt.guard.context, &context_type);
    let guard_state = typed_param(&evt.guard.state, machine_name);
    let guard_body = &evt.guard.body;

    let action_context = typed_param(&evt.action.context, &context_type);
    let action_state = typed_param(&evt.action.state, machine_name);
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
    let input_param_unused = if let Some(ref param) = evt.input {
        let ty = &param.ty;
        let prefixed = format_ident!("_{}", param.name);
        quote! { #prefixed: #ty }
    } else {
        quote! { _input: () }
    };

    // --- Output type ---
    let output_type = if let Some(ref ty) = evt.output_type {
        quote! { #ty }
    } else {
        quote! { () }
    };

    // --- Output function body ---
    let output_fn = if let Some(ref output) = evt.output {
        let out_context = typed_param(&output.context, &context_type);
        let out_state = typed_param(&output.state, machine_name);
        let out_body = &output.body;
        quote! {
            open spec fn output(#out_context, #out_state, #input_param) -> #output_type {
                #out_body
            }
        }
    } else {
        // No user-provided output block — emit a trivial `()` output.
        quote! {
            open spec fn output(_context: #context_type, _state: #machine_name, _input: #input_type) -> () {
                ()
            }
        }
    };

    let event_struct = quote! {
        #[allow(dead_code)]
        pub struct #event_name;
    };

    let (safety_span, safety_body, safety_params) = match &evt.safety_proof {
        Some(p) => {
            let ctx = typed_param(&p.context, &context_type);
            let st = typed_param(&p.state, machine_name);
            (p.span, { let b = &p.body; quote! { #b } }, quote! { #ctx, #st, #input_param })
        }
        None => (event_name.span(), quote! {}, quote! { _context: #context_type, _state: #machine_name, #input_param_unused }),
    };
    let event_impl = quote_spanned! { safety_span =>
        impl Event<#machine_name> for #event_name {
            type Input = #input_type;
            type Output = #output_type;

            open spec fn guard(#guard_context, #guard_state, #input_param) -> bool {
                #guard_body
            }

            open spec fn action(#action_context, #action_state, #input_param) -> #machine_name {
                #action_body
            }

            #output_fn

            proof fn proof_safety(#safety_params) {
                #safety_body
            }
        }
    };

    let refined_impl = if evt.refined {
        if let Some(ref refines_path) = decl.refines {
            let abstract_event = abstract_event_path(refines_path, event_name);

            // lift_in: map concrete input to abstract input.
            let lift_in_fn = if let Some(ref li) = evt.lift_in {
                let li_context = typed_param(&li.context, &context_type);
                let li_state = typed_param(&li.state, machine_name);
                let li_body = &li.body;
                quote! {
                    open spec fn lift_in(#li_context, #li_state, #input_param)
                        -> <#abstract_event as Event<#refines_path>>::Input
                    {
                        #li_body
                    }
                }
            } else if evt.input.is_some() {
                return Error::new(
                    evt.name.span(),
                    "refined event with an input must declare a 'lift_in: |context, state| ...' \
                     block mapping the concrete input to the abstract input",
                )
                .to_compile_error();
            } else {
                quote! {
                    open spec fn lift_in(_context: #context_type, _state: #machine_name, _input: #input_type)
                        -> <#abstract_event as Event<#refines_path>>::Input
                    {
                        ()
                    }
                }
            };

            // lift_out: map concrete output to abstract output.
            let lift_out_fn = if let Some(ref lo) = evt.lift_out {
                let lo_param = typed_param(&lo.param, &output_type);
                let lo_body = &lo.body;
                quote! {
                    open spec fn lift_out(#lo_param)
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

            let (_str_span, str_body, str_params) = match &evt.strengthening_proof {
                Some(p) => {
                    let ctx = typed_param(&p.context, &context_type);
                    let st = typed_param(&p.state, machine_name);
                    (p.span, { let b = &p.body; quote! { #b } }, quote! { #ctx, #st, #input_param })
                }
                None => (event_name.span(), quote! {}, quote! { _context: #context_type, _state: #machine_name, #input_param_unused }),
            };
            let (_sim_span, sim_body, sim_params) = match &evt.simulation_proof {
                Some(p) => {
                    let ctx = typed_param(&p.context, &context_type);
                    let st = typed_param(&p.state, machine_name);
                    (p.span, { let b = &p.body; quote! { #b } }, quote! { #ctx, #st, #input_param })
                }
                None => (event_name.span(), quote! {}, quote! { _context: #context_type, _state: #machine_name, #input_param_unused }),
            };
            let refined_span = evt.strengthening_proof.as_ref()
                .or(evt.simulation_proof.as_ref())
                .map(|p| p.span)
                .unwrap_or_else(|| event_name.span());
            quote_spanned! { refined_span =>
                impl RefinedEvent<#machine_name, #abstract_event> for #event_name {
                    #lift_in_fn
                    #lift_out_fn

                    proof fn proof_strengthening(#str_params) {
                        #str_body
                    }
                    proof fn proof_simulation(#sim_params) {
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
        let (stut_span, stut_body, stut_params) = match &evt.stuttering_proof {
            Some(p) => {
                let ctx = typed_param(&p.context, &context_type);
                let st = typed_param(&p.state, machine_name);
                (p.span, { let b = &p.body; quote! { #b } }, quote! { #ctx, #st, #input_param })
            }
            None => (event_name.span(), quote! {}, quote! { _context: #context_type, _state: #machine_name, #input_param_unused }),
        };
        let (conv_span, conv_body, conv_params) = match &evt.convergence_proof {
            Some(p) => {
                let ctx = typed_param(&p.context, &context_type);
                let st = typed_param(&p.state, machine_name);
                (p.span, { let b = &p.body; quote! { #b } }, quote! { #ctx, #st, #input_param })
            }
            None => (event_name.span(), quote! {}, quote! { _context: #context_type, _state: #machine_name, #input_param_unused }),
        };
        let conv_method = quote_spanned! { conv_span =>
            proof fn proof_convergent(#conv_params) {
                #conv_body
            }
        };
        let stut_method = quote_spanned! { stut_span =>
            proof fn proof_stuttering(#stut_params) {
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

use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use verus_syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    token, Error, Expr, ExprClosure, Ident, Pat, Path, Result, ReturnType, Token, Type,
};

mod kw {
    verus_syn::custom_keyword!(deadlock_free);
    verus_syn::custom_keyword!(machine);
    verus_syn::custom_keyword!(refines);
    verus_syn::custom_keyword!(context);
    verus_syn::custom_keyword!(valid);
    verus_syn::custom_keyword!(state);
    verus_syn::custom_keyword!(init);
    verus_syn::custom_keyword!(lift);
    verus_syn::custom_keyword!(lift_context);
    verus_syn::custom_keyword!(proof_lift_context_valid);
    verus_syn::custom_keyword!(proof_lift_safe);
    verus_syn::custom_keyword!(proof_deadlock_free);
    verus_syn::custom_keyword!(invariant);
    verus_syn::custom_keyword!(event);
    verus_syn::custom_keyword!(guard);
    verus_syn::custom_keyword!(action);
    verus_syn::custom_keyword!(variant);
    verus_syn::custom_keyword!(output);
    verus_syn::custom_keyword!(lift_in);
    verus_syn::custom_keyword!(lift_out);
    verus_syn::custom_keyword!(refined);
    verus_syn::custom_keyword!(concrete);
    verus_syn::custom_keyword!(proof_safety);
    verus_syn::custom_keyword!(proof_strengthening);
    verus_syn::custom_keyword!(proof_simulation);
    verus_syn::custom_keyword!(proof_convergent);
    verus_syn::custom_keyword!(proof_stuttering);
}

pub enum ContextDecl {
    /// External context declaration like `context: SomeType`.
    External(Type),
    /// Inline context declaration like `context { field1: type1, ... }`.
    /// Generates a struct named `Context` with the given fields.
    Inline {
        fields: Vec<StateField>,
        valid: Option<ValidDecl>,
    },
}

pub struct ValidDecl {
    pub context: ClosureParam,
    pub body: TokenStream,
}

impl ContextDecl {
    /// Return the spec-level type to use in trait impls and function signatures.
    /// For external context, this is the user-provided type.
    /// For inline context, this is `Context`.
    pub fn spec_type(&self) -> Type {
        match self {
            ContextDecl::External(ty) => ty.clone(),
            ContextDecl::Inline { .. } => verus_syn::parse_quote!(Context),
        }
    }
}

pub struct MacroInput {
    pub machine: Option<MachineDecl>,
}

pub struct MachineDecl {
    pub deadlock_free: Option<Span>,
    pub name: Ident,
    pub refines: Option<Path>,
    pub context: ContextDecl,
    pub state_fields: Vec<StateField>,
    pub init: InitDecl,
    pub lift: Option<LiftDecl>,
    pub lift_context: Option<LiftContextDecl>,
    pub proof_lift_context_valid: Option<LiftContextDecl>,
    pub proof_lift_safe: Option<FnBody>,
    pub proof_deadlock_free: Option<FnBody>,
    pub invariant: Option<InvariantDecl>,
    pub variant: Option<VariantDecl>,
    pub events: Vec<EventDecl>,
}

pub struct VariantDecl {
    pub context: ClosureParam,
    pub state: ClosureParam,
    pub ret_type: Type,
    pub body: TokenStream,
}

pub struct StateField {
    pub name: Ident,
    pub ty: Type,
}

pub struct InitDecl {
    pub context: ClosureParam,
    pub body: TokenStream,
}

pub struct LiftDecl {
    pub state: ClosureParam,
    pub body: TokenStream,
}

pub struct LiftContextDecl {
    pub context: ClosureParam,
    pub body: TokenStream,
}

pub struct InvariantDecl {
    pub context: ClosureParam,
    pub state: ClosureParam,
    pub body: TokenStream,
}

pub struct EventParam {
    pub name: Ident,
    pub ty: Type,
}

pub struct LiftFn {
    pub param: ClosureParam,
    pub body: TokenStream,
}

pub struct LiftInFn {
    pub context: ClosureParam,
    pub state: ClosureParam,
    pub body: TokenStream,
}

pub struct EventDecl {
    pub refined: bool,
    pub concrete: bool,
    pub name: Ident,
    pub input: Option<EventParam>,
    pub output_type: Option<Type>,
    pub guard: FnBody,
    pub action: FnBody,
    pub output: Option<FnBody>,
    pub lift_in: Option<LiftInFn>,
    pub lift_out: Option<LiftFn>,
    pub safety_proof: Option<FnBody>,
    pub strengthening_proof: Option<FnBody>,
    pub simulation_proof: Option<FnBody>,
    pub convergence_proof: Option<FnBody>,
    pub stuttering_proof: Option<FnBody>,
}

pub struct FnBody {
    pub span: Span,
    pub context: ClosureParam,
    pub state: ClosureParam,
    pub body: TokenStream,
}

pub struct ClosureParam {
    pub name: Ident,
    pub ty: Option<Type>,
}

impl Parse for StateField {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ty: Type = input.parse()?;
        Ok(StateField { name, ty })
    }
}

fn closure_param(pat: &Pat, index: usize) -> Result<ClosureParam> {
    match pat {
        Pat::Ident(p) => Ok(ClosureParam {
            name: p.ident.clone(),
            ty: None,
        }),
        Pat::Wild(w) => Ok(ClosureParam {
            name: Ident::new(&format!("_p{index}"), w.underscore_token.span),
            ty: None,
        }),
        Pat::Type(p) => {
            let name = match &*p.pat {
                Pat::Ident(pi) => pi.ident.clone(),
                Pat::Wild(w) => Ident::new(&format!("_p{index}"), w.underscore_token.span),
                other => {
                    return Err(Error::new_spanned(
                        other,
                        "closure parameter must be a plain identifier or `_`",
                    ))
                }
            };
            Ok(ClosureParam {
                name,
                ty: Some((*p.ty).clone()),
            })
        }
        other => Err(Error::new_spanned(
            other,
            "closure parameter must be a plain identifier or `_`",
        )),
    }
}

fn closure_params(closure: &ExprClosure) -> Result<Vec<ClosureParam>> {
    closure
        .inputs
        .iter()
        .enumerate()
        .map(|(i, arg)| closure_param(&arg.pat, i))
        .collect()
}

fn body_tokens(body: &Expr) -> TokenStream {
    match body {
        Expr::Block(b) if b.attrs.is_empty() && b.label.is_none() => {
            let stmts = &b.block.stmts;
            quote! { #(#stmts)* }
        }
        other => other.to_token_stream(),
    }
}

fn reject_output(closure: &ExprClosure, what: &str) -> Result<()> {
    if !matches!(closure.output, ReturnType::Default) {
        return Err(Error::new_spanned(
            &closure.output,
            format!("the `{what}` closure must not declare a return type"),
        ));
    }
    Ok(())
}

fn closure_1(closure: ExprClosure, what: &str) -> Result<(ClosureParam, TokenStream)> {
    reject_output(&closure, what)?;
    let mut params = closure_params(&closure)?;
    if params.len() != 1 {
        return Err(Error::new_spanned(
            &closure.or1_token,
            format!("the `{what}` closure expects one parameter, like `|context|`"),
        ));
    }
    Ok((params.remove(0), body_tokens(&closure.body)))
}

fn closure_2(closure: ExprClosure, what: &str) -> Result<(ClosureParam, ClosureParam, TokenStream)> {
    reject_output(&closure, what)?;
    let mut params = closure_params(&closure)?;
    if params.len() != 2 {
        return Err(Error::new_spanned(
            &closure.or1_token,
            format!("the `{what}` closure expects two parameters, like `|context, state|`"),
        ));
    }
    let body = body_tokens(&closure.body);
    let state = params.remove(1);
    let context = params.remove(0);
    Ok((context, state, body))
}

fn fn_body(closure: ExprClosure, what: &str, span: Span) -> Result<FnBody> {
    let (context, state, body) = closure_2(closure, what)?;
    Ok(FnBody {
        span,
        context,
        state,
        body,
    })
}

fn eat_comma(input: ParseStream) -> Result<()> {
    if input.peek(Token![,]) {
        input.parse::<Token![,]>()?;
    }
    Ok(())
}

fn parse_event(content: ParseStream) -> Result<EventDecl> {
    let mut refined = false;
    let mut concrete = false;

    // Parse optional modifiers before 'event'
    while !content.peek(kw::event) {
        if content.peek(kw::refined) {
            content.parse::<kw::refined>()?;
            refined = true;
        } else if content.peek(kw::concrete) {
            content.parse::<kw::concrete>()?;
            concrete = true;
        } else {
            return Err(content.error("expected 'event', 'refined', or 'concrete'"));
        }
    }

    content.parse::<kw::event>()?;
    let name: Ident = content.parse()?;

    // Parse optional input: event Name(param: Type)
    let input = if content.peek(token::Paren) {
        let params;
        parenthesized!(params in content);
        let param_name: Ident = params.parse()?;
        params.parse::<Token![:]>()?;
        let param_ty: Type = params.parse()?;
        Some(EventParam {
            name: param_name,
            ty: param_ty,
        })
    } else {
        None
    };

    // Parse optional output type: -> Type
    let output_type = if content.peek(Token![->]) {
        content.parse::<Token![->]>()?;
        Some(content.parse::<Type>()?)
    } else {
        None
    };

    let event_content;
    braced!(event_content in content);

    let mut guard = None;
    let mut action = None;
    let mut output = None;
    let mut lift_in = None;
    let mut lift_out = None;
    let mut safety_proof = None;
    let mut strengthening_proof = None;
    let mut simulation_proof = None;
    let mut convergence_proof = None;
    let mut stuttering_proof = None;

    while !event_content.is_empty() {
        if event_content.peek(kw::guard) {
            let kw = event_content.parse::<kw::guard>()?;
            event_content.parse::<Token![:]>()?;
            guard = Some(fn_body(event_content.parse()?, "guard", kw.span)?);
        } else if event_content.peek(kw::action) {
            let kw = event_content.parse::<kw::action>()?;
            event_content.parse::<Token![:]>()?;
            action = Some(fn_body(event_content.parse()?, "action", kw.span)?);
        } else if event_content.peek(kw::output) {
            let kw = event_content.parse::<kw::output>()?;
            event_content.parse::<Token![:]>()?;
            output = Some(fn_body(event_content.parse()?, "output", kw.span)?);
        } else if event_content.peek(kw::lift_in) {
            event_content.parse::<kw::lift_in>()?;
            event_content.parse::<Token![:]>()?;
            let (context, state, body) = closure_2(event_content.parse()?, "lift_in")?;
            lift_in = Some(LiftInFn {
                context,
                state,
                body,
            });
        } else if event_content.peek(kw::lift_out) {
            event_content.parse::<kw::lift_out>()?;
            event_content.parse::<Token![:]>()?;
            let (param, body) = closure_1(event_content.parse()?, "lift_out")?;
            lift_out = Some(LiftFn { param, body });
        } else if event_content.peek(kw::proof_safety) {
            let kw = event_content.parse::<kw::proof_safety>()?;
            event_content.parse::<Token![:]>()?;
            safety_proof = Some(fn_body(event_content.parse()?, "proof_safety", kw.span)?);
        } else if event_content.peek(kw::proof_strengthening) {
            let kw = event_content.parse::<kw::proof_strengthening>()?;
            event_content.parse::<Token![:]>()?;
            strengthening_proof =
                Some(fn_body(event_content.parse()?, "proof_strengthening", kw.span)?);
        } else if event_content.peek(kw::proof_simulation) {
            let kw = event_content.parse::<kw::proof_simulation>()?;
            event_content.parse::<Token![:]>()?;
            simulation_proof =
                Some(fn_body(event_content.parse()?, "proof_simulation", kw.span)?);
        } else if event_content.peek(kw::proof_convergent) {
            let kw = event_content.parse::<kw::proof_convergent>()?;
            event_content.parse::<Token![:]>()?;
            convergence_proof =
                Some(fn_body(event_content.parse()?, "proof_convergent", kw.span)?);
        } else if event_content.peek(kw::proof_stuttering) {
            let kw = event_content.parse::<kw::proof_stuttering>()?;
            event_content.parse::<Token![:]>()?;
            stuttering_proof =
                Some(fn_body(event_content.parse()?, "proof_stuttering", kw.span)?);
        } else {
            return Err(event_content.error(
                "expected 'guard', 'action', 'output', 'lift_in', 'lift_out', or a proof block",
            ));
        }
        eat_comma(&event_content)?;
    }

    let name_span = name.span();
    Ok(EventDecl {
        refined,
        concrete,
        name,
        input,
        output_type,
        guard: guard.ok_or_else(|| Error::new(name_span, "event missing 'guard'"))?,
        action: action.ok_or_else(|| Error::new(name_span, "event missing 'action'"))?,
        output,
        lift_in,
        lift_out,
        safety_proof,
        strengthening_proof,
        simulation_proof,
        convergence_proof,
        stuttering_proof,
    })
}

impl Parse for MacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let machine = if input.is_empty() {
            None
        } else {
            Some(input.parse::<MachineDecl>()?)
        };
        Ok(MacroInput { machine })
    }
}

impl Parse for MachineDecl {
    fn parse(input: ParseStream) -> Result<Self> {
        // Parse optional 'deadlock_free'
        let deadlock_free = if input.peek(kw::deadlock_free) {
            Some(input.parse::<kw::deadlock_free>()?.span)
        } else {
            None
        };

        // Parse 'machine'
        input.parse::<kw::machine>()?;

        // Parse machine name
        let name: Ident = input.parse()?;

        // Parse optional 'refines Path'
        let refines = if input.peek(kw::refines) {
            input.parse::<kw::refines>()?;
            Some(input.parse::<Path>()?)
        } else {
            None
        };

        // Parse machine body
        let content;
        braced!(content in input);

        // Context is first
        content.parse::<kw::context>()?;
        let mut context = if content.peek(Token![:]) {
            // External: context: SomeType
            content.parse::<Token![:]>()?;
            let context_type: Type = content.parse()?;
            ContextDecl::External(context_type)
        } else {
            // Inline: context { field: type, ... }
            let context_content;
            braced!(context_content in content);
            let fields: Punctuated<StateField, Token![,]> =
                context_content.parse_terminated(StateField::parse, Token![,])?;
            ContextDecl::Inline {
                fields: fields.into_iter().collect(),
                valid: None, // parsed below if present
            }
        };
        eat_comma(&content)?;

        // Parse remaining items in any order
        let mut state_fields = None;
        let mut init = None;
        let mut lift = None;
        let mut lift_context = None;
        let mut proof_lift_context_valid = None;
        let mut proof_lift_safe = None;
        let mut proof_deadlock_free = None;
        let mut invariant = None;
        let mut variant = None;
        let mut events = Vec::new();

        while !content.is_empty() {
            if content.peek(kw::valid) {
                content.parse::<kw::valid>()?;
                content.parse::<Token![:]>()?;
                let (param, body) = closure_1(content.parse()?, "valid")?;
                match &mut context {
                    ContextDecl::Inline { valid, .. } => {
                        *valid = Some(ValidDecl {
                            context: param,
                            body,
                        });
                    }
                    ContextDecl::External(_) => {
                        return Err(Error::new_spanned(
                            &param.name,
                            "'valid' can only be used with an inline `context { ... }` declaration",
                        ));
                    }
                }
            } else if content.peek(kw::state) {
                content.parse::<kw::state>()?;
                let state_content;
                braced!(state_content in content);
                let fields: Punctuated<StateField, Token![,]> =
                    state_content.parse_terminated(StateField::parse, Token![,])?;
                state_fields = Some(fields.into_iter().collect());
            } else if content.peek(kw::init) {
                content.parse::<kw::init>()?;
                content.parse::<Token![:]>()?;
                let (context, body) = closure_1(content.parse()?, "init")?;
                init = Some(InitDecl { context, body });
            } else if content.peek(kw::lift) {
                content.parse::<kw::lift>()?;
                content.parse::<Token![:]>()?;
                let (state, body) = closure_1(content.parse()?, "lift")?;
                lift = Some(LiftDecl { state, body });
            } else if content.peek(kw::lift_context) {
                content.parse::<kw::lift_context>()?;
                content.parse::<Token![:]>()?;
                let (context, body) = closure_1(content.parse()?, "lift_context")?;
                lift_context = Some(LiftContextDecl { context, body });
            } else if content.peek(kw::proof_lift_context_valid) {
                content.parse::<kw::proof_lift_context_valid>()?;
                content.parse::<Token![:]>()?;
                let (context, body) = closure_1(content.parse()?, "proof_lift_context_valid")?;
                proof_lift_context_valid = Some(LiftContextDecl { context, body });
            } else if content.peek(kw::proof_lift_safe) {
                let kw = content.parse::<kw::proof_lift_safe>()?;
                content.parse::<Token![:]>()?;
                proof_lift_safe = Some(fn_body(content.parse()?, "proof_lift_safe", kw.span)?);
            } else if content.peek(kw::proof_deadlock_free) {
                let kw = content.parse::<kw::proof_deadlock_free>()?;
                content.parse::<Token![:]>()?;
                proof_deadlock_free =
                    Some(fn_body(content.parse()?, "proof_deadlock_free", kw.span)?);
            } else if content.peek(kw::invariant) {
                content.parse::<kw::invariant>()?;
                content.parse::<Token![:]>()?;
                let (context, state, body) = closure_2(content.parse()?, "invariant")?;
                invariant = Some(InvariantDecl {
                    context,
                    state,
                    body,
                });
            } else if content.peek(kw::variant) {
                content.parse::<kw::variant>()?;
                content.parse::<Token![:]>()?;
                let closure: ExprClosure = content.parse()?;
                let mut params = closure_params(&closure)?;
                if params.len() != 2 {
                    return Err(Error::new_spanned(
                        &closure.or1_token,
                        "the `variant` closure expects two parameters, like `|context, state|`",
                    ));
                }
                let ret_type = match &closure.output {
                    ReturnType::Type(.., ty) => (**ty).clone(),
                    ReturnType::Default => {
                        return Err(Error::new_spanned(
                            &closure.or2_token,
                            "`variant` must declare its return type, like \
                             `variant: |context, state| -> (nat, nat) { ... }`",
                        ));
                    }
                };
                let body = body_tokens(&closure.body);
                let state = params.remove(1);
                let context = params.remove(0);
                variant = Some(VariantDecl {
                    context,
                    state,
                    ret_type,
                    body,
                });
            } else if content.peek(kw::event)
                || content.peek(kw::refined)
                || content.peek(kw::concrete)
            {
                events.push(parse_event(&content)?);
            } else {
                return Err(content.error(
                    "expected 'state', 'valid', 'init', 'lift', 'lift_context', \
                     'proof_lift_context_valid', 'proof_lift_safe', 'proof_deadlock_free', \
                     'invariant', 'variant', or an event declaration",
                ));
            }
            eat_comma(&content)?;
        }

        let name_span = name.span();
        Ok(MachineDecl {
            deadlock_free,
            name,
            refines,
            context,
            state_fields: state_fields.unwrap_or_default(),
            init: init.ok_or_else(|| Error::new(name_span, "missing 'init' block"))?,
            lift,
            lift_context,
            proof_lift_context_valid,
            proof_lift_safe,
            proof_deadlock_free,
            invariant,
            variant,
            events,
        })
    }
}

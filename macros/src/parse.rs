use proc_macro2::{Span, TokenStream, TokenTree};
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    Ident, Path, Result, Token, Type,
};

mod kw {
    syn::custom_keyword!(deadlock_free);
    syn::custom_keyword!(machine);
    syn::custom_keyword!(refines);
    syn::custom_keyword!(context);
    syn::custom_keyword!(valid);
    syn::custom_keyword!(state);
    syn::custom_keyword!(init);
    syn::custom_keyword!(lift);
    syn::custom_keyword!(lift_context);
    syn::custom_keyword!(proof_lift_context_valid);
    syn::custom_keyword!(proof_lift_safe);
    syn::custom_keyword!(invariant);
    syn::custom_keyword!(event);
    syn::custom_keyword!(guard);
    syn::custom_keyword!(action);
    syn::custom_keyword!(variant);
    syn::custom_keyword!(output);
    syn::custom_keyword!(lift_in);
    syn::custom_keyword!(lift_out);
    syn::custom_keyword!(refined);
    syn::custom_keyword!(concrete);
    syn::custom_keyword!(proof_safety);
    syn::custom_keyword!(proof_strengthening);
    syn::custom_keyword!(proof_simulation);
    syn::custom_keyword!(proof_convergent);
    syn::custom_keyword!(proof_stuttering);
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
            ContextDecl::Inline { .. } => syn::parse_quote!(Context),
        }
    }
}

pub struct MacroInput {
    pub machine: Option<MachineDecl>,
}

pub struct MachineDecl {
    pub deadlock_free: bool,
    pub name: Ident,
    pub refines: Option<Path>,
    pub context: ContextDecl,
    pub state_fields: Vec<StateField>,
    pub init: InitDecl,
    pub lift: Option<LiftDecl>,
    pub lift_context: Option<LiftContextDecl>,
    pub proof_lift_context_valid: Option<LiftContextDecl>,
    pub proof_lift_safe: Option<FnBody>,
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

struct ClosureSig {
    pipe_span: Span,
    params: Vec<ClosureParam>,
    ret_type: Option<Type>,
    body: TokenStream,
}

impl Parse for StateField {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ty: Type = input.parse()?;
        Ok(StateField { name, ty })
    }
}

fn parse_closure_param(input: ParseStream, index: usize) -> Result<ClosureParam> {
    let name = if input.peek(Token![_]) {
        let underscore = input.parse::<Token![_]>()?;
        Ident::new(&format!("_p{index}"), underscore.span)
    } else {
        input.parse::<Ident>()?
    };
    let ty = if input.peek(Token![:]) {
        input.parse::<Token![:]>()?;
        Some(input.parse::<Type>()?)
    } else {
        None
    };
    Ok(ClosureParam { name, ty })
}

fn parse_closure(input: ParseStream) -> Result<ClosureSig> {
    let pipe_span = input.span();

    let mut params = Vec::new();
    if input.peek(Token![||]) {
        input.parse::<Token![||]>()?;
    } else {
        input.parse::<Token![|]>()?;
        while !input.peek(Token![|]) {
            params.push(parse_closure_param(input, params.len())?);
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            } else {
                break;
            }
        }
        input.parse::<Token![|]>()?;
    }

    let ret_type = if input.peek(Token![->]) {
        input.parse::<Token![->]>()?;
        Some(input.parse::<Type>()?)
    } else {
        None
    };

    let body = if input.peek(syn::token::Brace) {
        let content;
        braced!(content in input);
        content.parse::<TokenStream>()?
    } else {
        if ret_type.is_some() {
            return Err(input.error("a closure with a return type must have a `{ ... }` body"));
        }
        let mut tokens = Vec::new();
        while !input.is_empty() && !input.peek(Token![,]) {
            tokens.push(input.parse::<TokenTree>()?);
        }
        if tokens.is_empty() {
            return Err(input.error("expected a closure body after `|...|`"));
        }
        tokens.into_iter().collect()
    };

    Ok(ClosureSig {
        pipe_span,
        params,
        ret_type,
        body,
    })
}

fn eat_comma(input: ParseStream) -> Result<()> {
    if input.peek(Token![,]) {
        input.parse::<Token![,]>()?;
    }
    Ok(())
}

fn reject_ret_type(c: &ClosureSig, what: &str) -> Result<()> {
    if c.ret_type.is_some() {
        return Err(syn::Error::new(
            c.pipe_span,
            format!("the `{what}` closure must not declare a return type"),
        ));
    }
    Ok(())
}

fn closure_1(c: ClosureSig, what: &str) -> Result<(ClosureParam, TokenStream)> {
    reject_ret_type(&c, what)?;
    if c.params.len() != 1 {
        return Err(syn::Error::new(
            c.pipe_span,
            format!("the `{what}` closure expects one parameter, like `|context|`"),
        ));
    }
    let body = c.body;
    Ok((c.params.into_iter().next().unwrap(), body))
}

fn closure_2(c: ClosureSig, what: &str) -> Result<(ClosureParam, ClosureParam, TokenStream)> {
    reject_ret_type(&c, what)?;
    if c.params.len() != 2 {
        return Err(syn::Error::new(
            c.pipe_span,
            format!("the `{what}` closure expects two parameters, like `|context, state|`"),
        ));
    }
    let body = c.body;
    let mut it = c.params.into_iter();
    Ok((it.next().unwrap(), it.next().unwrap(), body))
}

fn fn_body(c: ClosureSig, what: &str, span: Span) -> Result<FnBody> {
    let (context, state, body) = closure_2(c, what)?;
    Ok(FnBody {
        span,
        context,
        state,
        body,
    })
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
    let input = if content.peek(syn::token::Paren) {
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
            guard = Some(fn_body(parse_closure(&event_content)?, "guard", kw.span)?);
        } else if event_content.peek(kw::action) {
            let kw = event_content.parse::<kw::action>()?;
            event_content.parse::<Token![:]>()?;
            action = Some(fn_body(parse_closure(&event_content)?, "action", kw.span)?);
        } else if event_content.peek(kw::output) {
            let kw = event_content.parse::<kw::output>()?;
            event_content.parse::<Token![:]>()?;
            output = Some(fn_body(parse_closure(&event_content)?, "output", kw.span)?);
        } else if event_content.peek(kw::lift_in) {
            event_content.parse::<kw::lift_in>()?;
            event_content.parse::<Token![:]>()?;
            let (context, state, body) = closure_2(parse_closure(&event_content)?, "lift_in")?;
            lift_in = Some(LiftInFn {
                context,
                state,
                body,
            });
        } else if event_content.peek(kw::lift_out) {
            event_content.parse::<kw::lift_out>()?;
            event_content.parse::<Token![:]>()?;
            let (param, body) = closure_1(parse_closure(&event_content)?, "lift_out")?;
            lift_out = Some(LiftFn { param, body });
        } else if event_content.peek(kw::proof_safety) {
            let kw = event_content.parse::<kw::proof_safety>()?;
            event_content.parse::<Token![:]>()?;
            safety_proof = Some(fn_body(parse_closure(&event_content)?, "proof_safety", kw.span)?);
        } else if event_content.peek(kw::proof_strengthening) {
            let kw = event_content.parse::<kw::proof_strengthening>()?;
            event_content.parse::<Token![:]>()?;
            strengthening_proof = Some(fn_body(
                parse_closure(&event_content)?,
                "proof_strengthening",
                kw.span,
            )?);
        } else if event_content.peek(kw::proof_simulation) {
            let kw = event_content.parse::<kw::proof_simulation>()?;
            event_content.parse::<Token![:]>()?;
            simulation_proof = Some(fn_body(
                parse_closure(&event_content)?,
                "proof_simulation",
                kw.span,
            )?);
        } else if event_content.peek(kw::proof_convergent) {
            let kw = event_content.parse::<kw::proof_convergent>()?;
            event_content.parse::<Token![:]>()?;
            convergence_proof = Some(fn_body(
                parse_closure(&event_content)?,
                "proof_convergent",
                kw.span,
            )?);
        } else if event_content.peek(kw::proof_stuttering) {
            let kw = event_content.parse::<kw::proof_stuttering>()?;
            event_content.parse::<Token![:]>()?;
            stuttering_proof = Some(fn_body(
                parse_closure(&event_content)?,
                "proof_stuttering",
                kw.span,
            )?);
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
        guard: guard.ok_or_else(|| syn::Error::new(name_span, "event missing 'guard'"))?,
        action: action.ok_or_else(|| syn::Error::new(name_span, "event missing 'action'"))?,
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
        let deadlock_free = input.peek(kw::deadlock_free);
        if deadlock_free {
            input.parse::<kw::deadlock_free>()?;
        }

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
        let mut invariant = None;
        let mut variant = None;
        let mut events = Vec::new();

        while !content.is_empty() {
            if content.peek(kw::valid) {
                content.parse::<kw::valid>()?;
                content.parse::<Token![:]>()?;
                let (param, body) = closure_1(parse_closure(&content)?, "valid")?;
                match &mut context {
                    ContextDecl::Inline { valid, .. } => {
                        *valid = Some(ValidDecl {
                            context: param,
                            body,
                        });
                    }
                    ContextDecl::External(_) => {
                        return Err(syn::Error::new(
                            param.name.span(),
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
                let (context, body) = closure_1(parse_closure(&content)?, "init")?;
                init = Some(InitDecl { context, body });
            } else if content.peek(kw::lift) {
                content.parse::<kw::lift>()?;
                content.parse::<Token![:]>()?;
                let (state, body) = closure_1(parse_closure(&content)?, "lift")?;
                lift = Some(LiftDecl { state, body });
            } else if content.peek(kw::lift_context) {
                content.parse::<kw::lift_context>()?;
                content.parse::<Token![:]>()?;
                let (context, body) = closure_1(parse_closure(&content)?, "lift_context")?;
                lift_context = Some(LiftContextDecl { context, body });
            } else if content.peek(kw::proof_lift_context_valid) {
                content.parse::<kw::proof_lift_context_valid>()?;
                content.parse::<Token![:]>()?;
                let (context, body) =
                    closure_1(parse_closure(&content)?, "proof_lift_context_valid")?;
                proof_lift_context_valid = Some(LiftContextDecl { context, body });
            } else if content.peek(kw::proof_lift_safe) {
                let kw = content.parse::<kw::proof_lift_safe>()?;
                content.parse::<Token![:]>()?;
                proof_lift_safe =
                    Some(fn_body(parse_closure(&content)?, "proof_lift_safe", kw.span)?);
            } else if content.peek(kw::invariant) {
                content.parse::<kw::invariant>()?;
                content.parse::<Token![:]>()?;
                let (context, state, body) = closure_2(parse_closure(&content)?, "invariant")?;
                invariant = Some(InvariantDecl {
                    context,
                    state,
                    body,
                });
            } else if content.peek(kw::variant) {
                content.parse::<kw::variant>()?;
                content.parse::<Token![:]>()?;
                let c = parse_closure(&content)?;
                if c.params.len() != 2 {
                    return Err(syn::Error::new(
                        c.pipe_span,
                        "the `variant` closure expects two parameters, like `|context, state|`",
                    ));
                }
                let ret_type = c.ret_type.clone().ok_or_else(|| {
                    syn::Error::new(
                        c.pipe_span,
                        "`variant` must declare its return type, like \
                         `variant: |context, state| -> (nat, nat) { ... }`",
                    )
                })?;
                let body = c.body;
                let mut params = c.params.into_iter();
                variant = Some(VariantDecl {
                    context: params.next().unwrap(),
                    state: params.next().unwrap(),
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
                     'proof_lift_context_valid', 'proof_lift_safe', 'invariant', 'variant', \
                     or an event declaration",
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
            init: init.ok_or_else(|| syn::Error::new(name_span, "missing 'init' block"))?,
            lift,
            lift_context,
            proof_lift_context_valid,
            proof_lift_safe,
            invariant,
            variant,
            events,
        })
    }
}

use proc_macro2::TokenStream;
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
    syn::custom_keyword!(ctx);
    syn::custom_keyword!(valid);
    syn::custom_keyword!(state);
    syn::custom_keyword!(init);
    syn::custom_keyword!(lift);
    syn::custom_keyword!(lift_ctx);
    syn::custom_keyword!(proof_lift_ctx_valid);
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
    syn::custom_keyword!(safety_proof);
    syn::custom_keyword!(strengthening_proof);
    syn::custom_keyword!(simulation_proof);
    syn::custom_keyword!(convergence_proof);
    syn::custom_keyword!(stuttering_proof);
}

pub enum CtxDecl {
    /// `ctx: SomeType` — reference to an externally-defined context type.
    External(Type),
    /// `ctx { field: type, ... }` — inline context declaration.
    /// Generates a `Ctx` struct in both spec and exec scopes.
    Inline {
        fields: Vec<StateField>,
        valid: Option<ValidDecl>,
    },
}

pub struct ValidDecl {
    pub ctx_name: Ident,
    pub body: TokenStream,
}

impl CtxDecl {
    /// Return the spec-level type to use in trait impls and function signatures.
    /// For external ctx, this is the user-provided type.
    /// For inline ctx, this is `Ctx`.
    pub fn spec_type(&self) -> Type {
        match self {
            CtxDecl::External(ty) => ty.clone(),
            CtxDecl::Inline { .. } => syn::parse_quote!(Ctx),
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
    pub ctx: CtxDecl,
    pub state_fields: Vec<StateField>,
    pub init: InitDecl,
    pub lift: Option<LiftDecl>,
    pub lift_ctx: Option<LiftCtxDecl>,
    pub proof_lift_ctx_valid: Option<LiftCtxDecl>,
    pub proof_lift_safe: Option<FnBody>,
    pub invariant: Option<InvariantDecl>,
    pub variant: Option<VariantDecl>,
    pub events: Vec<EventDecl>,
}

pub struct VariantDecl {
    pub ctx_name: Ident,
    pub state_name: Ident,
    pub ret_type: Type,
    pub body: TokenStream,
}

pub struct StateField {
    pub name: Ident,
    pub ty: Type,
}

pub struct InitDecl {
    pub ctx_name: Ident,
    pub body: TokenStream,
}

pub struct LiftDecl {
    pub state_name: Ident,
    pub body: TokenStream,
}

pub struct LiftCtxDecl {
    pub ctx_name: Ident,
    pub body: TokenStream,
}

pub struct InvariantDecl {
    pub ctx_name: Ident,
    pub state_name: Ident,
    pub body: TokenStream,
}

pub struct EventParam {
    pub name: Ident,
    pub ty: Type,
}

pub struct LiftFn {
    pub param_name: Ident,
    pub body: TokenStream,
}

pub struct LiftInFn {
    pub ctx_name: Ident,
    pub state_name: Ident,
    pub input_name: Ident,
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
    pub span: proc_macro2::Span,
    pub ctx_name: Ident,
    pub state_name: Ident,
    pub body: TokenStream,
}

impl Parse for StateField {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ty: Type = input.parse()?;
        Ok(StateField { name, ty })
    }
}

fn parse_fn_body(input: ParseStream, span: proc_macro2::Span) -> Result<FnBody> {
    let params;
    parenthesized!(params in input);
    let ctx_name: Ident = params.parse()?;
    params.parse::<Token![,]>()?;
    let state_name: Ident = params.parse()?;
    let body_content;
    braced!(body_content in input);
    let body: TokenStream = body_content.parse()?;
    Ok(FnBody {
        span,
        ctx_name,
        state_name,
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
        Some(EventParam { name: param_name, ty: param_ty })
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
            guard = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::action) {
            let kw = event_content.parse::<kw::action>()?;
            action = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::output) {
            let kw = event_content.parse::<kw::output>()?;
            output = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::lift_in) {
            event_content.parse::<kw::lift_in>()?;
            let params;
            parenthesized!(params in event_content);
            let ctx_name: Ident = params.parse()?;
            params.parse::<Token![,]>()?;
            let state_name: Ident = params.parse()?;
            params.parse::<Token![,]>()?;
            let input_name: Ident = params.parse()?;
            let body_content;
            braced!(body_content in event_content);
            let body: TokenStream = body_content.parse()?;
            lift_in = Some(LiftInFn { ctx_name, state_name, input_name, body });
        } else if event_content.peek(kw::lift_out) {
            event_content.parse::<kw::lift_out>()?;
            let params;
            parenthesized!(params in event_content);
            let param_name: Ident = params.parse()?;
            let body_content;
            braced!(body_content in event_content);
            let body: TokenStream = body_content.parse()?;
            lift_out = Some(LiftFn { param_name, body });
        } else if event_content.peek(kw::safety_proof) {
            let kw = event_content.parse::<kw::safety_proof>()?;
            safety_proof = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::strengthening_proof) {
            let kw = event_content.parse::<kw::strengthening_proof>()?;
            strengthening_proof = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::simulation_proof) {
            let kw = event_content.parse::<kw::simulation_proof>()?;
            simulation_proof = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::convergence_proof) {
            let kw = event_content.parse::<kw::convergence_proof>()?;
            convergence_proof = Some(parse_fn_body(&event_content, kw.span)?);
        } else if event_content.peek(kw::stuttering_proof) {
            let kw = event_content.parse::<kw::stuttering_proof>()?;
            stuttering_proof = Some(parse_fn_body(&event_content, kw.span)?);
        } else {
            return Err(event_content.error(
                "expected 'guard', 'action', 'output', 'lift_in', 'lift_out', or proof block",
            ));
        }
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

        // First item: ctx: Type  OR  ctx { fields... }
        content.parse::<kw::ctx>()?;
        let mut ctx = if content.peek(Token![:]) {
            // External: ctx: SomeType
            content.parse::<Token![:]>()?;
            let ctx_type: Type = content.parse()?;
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
            }
            CtxDecl::External(ctx_type)
        } else {
            // Inline: ctx { field: type, ... }
            let ctx_content;
            braced!(ctx_content in content);
            let fields: Punctuated<StateField, Token![,]> =
                ctx_content.parse_terminated(StateField::parse, Token![,])?;
            CtxDecl::Inline {
                fields: fields.into_iter().collect(),
                valid: None, // parsed below if present
            }
        };

        // Parse remaining items in any order
        let mut state_fields = None;
        let mut init = None;
        let mut lift = None;
        let mut lift_ctx = None;
        let mut proof_lift_ctx_valid = None;
        let mut proof_lift_safe = None;
        let mut invariant = None;
        let mut variant = None;
        let mut events = Vec::new();

        while !content.is_empty() {
            if content.peek(kw::valid) {
                content.parse::<kw::valid>()?;
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                match &mut ctx {
                    CtxDecl::Inline { ref mut valid, .. } => {
                        *valid = Some(ValidDecl { ctx_name, body });
                    }
                    CtxDecl::External(_) => {
                        return Err(content.error(
                            "'valid' block can only be used with inline ctx { } declaration",
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
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                init = Some(InitDecl { ctx_name, body });
            } else if content.peek(kw::lift) {
                content.parse::<kw::lift>()?;
                let params;
                parenthesized!(params in content);
                let state_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                lift = Some(LiftDecl { state_name, body });
            } else if content.peek(kw::lift_ctx) {
                content.parse::<kw::lift_ctx>()?;
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                lift_ctx = Some(LiftCtxDecl { ctx_name, body });
            } else if content.peek(kw::proof_lift_ctx_valid) {
                content.parse::<kw::proof_lift_ctx_valid>()?;
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                proof_lift_ctx_valid = Some(LiftCtxDecl { ctx_name, body });
            } else if content.peek(kw::proof_lift_safe) {
                let kw = content.parse::<kw::proof_lift_safe>()?;
                proof_lift_safe = Some(parse_fn_body(&content, kw.span)?);
            } else if content.peek(kw::invariant) {
                content.parse::<kw::invariant>()?;
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                params.parse::<Token![,]>()?;
                let state_name: Ident = params.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                invariant = Some(InvariantDecl {
                    ctx_name,
                    state_name,
                    body,
                });
            } else if content.peek(kw::variant) {
                content.parse::<kw::variant>()?;
                let params;
                parenthesized!(params in content);
                let ctx_name: Ident = params.parse()?;
                params.parse::<Token![,]>()?;
                let state_name: Ident = params.parse()?;
                content.parse::<Token![->]>()?;
                let ret_type: Type = content.parse()?;
                let body_content;
                braced!(body_content in content);
                let body: TokenStream = body_content.parse()?;
                variant = Some(VariantDecl {
                    ctx_name,
                    state_name,
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
                    "expected 'state', 'valid', 'init', 'lift', 'lift_ctx', \
                     'proof_lift_ctx_valid', 'proof_lift_safe', 'invariant', 'variant', \
                     or event declaration",
                ));
            }
        }

        let name_span = name.span();
        Ok(MachineDecl {
            deadlock_free,
            name,
            refines,
            ctx,
            state_fields: state_fields.unwrap_or_default(),
            init: init.ok_or_else(|| syn::Error::new(name_span, "missing 'init' block"))?,
            lift,
            lift_ctx,
            proof_lift_ctx_valid,
            proof_lift_safe,
            invariant,
            variant,
            events,
        })
    }
}

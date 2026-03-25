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
    syn::custom_keyword!(state);
    syn::custom_keyword!(init);
    syn::custom_keyword!(lift);
    syn::custom_keyword!(invariant);
    syn::custom_keyword!(event);
    syn::custom_keyword!(guard);
    syn::custom_keyword!(action);
    syn::custom_keyword!(variant);
    syn::custom_keyword!(refined);
    syn::custom_keyword!(concrete);
    syn::custom_keyword!(convergent);
}

pub struct MachineDecl {
    pub deadlock_free: bool,
    pub name: Ident,
    pub refines: Option<Path>,
    pub ctx_type: Type,
    pub state_fields: Vec<StateField>,
    pub init: InitDecl,
    pub lift: Option<LiftDecl>,
    pub invariant: Option<InvariantDecl>,
    pub events: Vec<EventDecl>,
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

pub struct InvariantDecl {
    pub ctx_name: Ident,
    pub state_name: Ident,
    pub body: TokenStream,
}

pub struct EventDecl {
    pub refined: bool,
    pub concrete: bool,
    pub convergent: bool,
    pub name: Ident,
    pub guard: FnBody,
    pub action: FnBody,
    pub variant: Option<FnBody>,
}

pub struct FnBody {
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

fn parse_fn_body(input: ParseStream) -> Result<FnBody> {
    let params;
    parenthesized!(params in input);
    let ctx_name: Ident = params.parse()?;
    params.parse::<Token![,]>()?;
    let state_name: Ident = params.parse()?;
    let body_content;
    braced!(body_content in input);
    let body: TokenStream = body_content.parse()?;
    Ok(FnBody {
        ctx_name,
        state_name,
        body,
    })
}

fn parse_event(content: ParseStream) -> Result<EventDecl> {
    let mut refined = false;
    let mut concrete = false;
    let mut convergent = false;

    // Parse optional modifiers before 'event'
    while !content.peek(kw::event) {
        if content.peek(kw::refined) {
            content.parse::<kw::refined>()?;
            refined = true;
        } else if content.peek(kw::concrete) {
            content.parse::<kw::concrete>()?;
            concrete = true;
        } else if content.peek(kw::convergent) {
            content.parse::<kw::convergent>()?;
            convergent = true;
        } else {
            return Err(content.error("expected 'event', 'refined', 'concrete', or 'convergent'"));
        }
    }

    content.parse::<kw::event>()?;
    let name: Ident = content.parse()?;

    let event_content;
    braced!(event_content in content);

    let mut guard = None;
    let mut action = None;
    let mut variant = None;

    while !event_content.is_empty() {
        if event_content.peek(kw::guard) {
            event_content.parse::<kw::guard>()?;
            guard = Some(parse_fn_body(&event_content)?);
        } else if event_content.peek(kw::action) {
            event_content.parse::<kw::action>()?;
            action = Some(parse_fn_body(&event_content)?);
        } else if event_content.peek(kw::variant) {
            event_content.parse::<kw::variant>()?;
            variant = Some(parse_fn_body(&event_content)?);
        } else {
            return Err(event_content.error("expected 'guard', 'action', or 'variant'"));
        }
    }

    let name_span = name.span();
    Ok(EventDecl {
        refined,
        concrete,
        convergent,
        name,
        guard: guard.ok_or_else(|| syn::Error::new(name_span, "event missing 'guard'"))?,
        action: action.ok_or_else(|| syn::Error::new(name_span, "event missing 'action'"))?,
        variant,
    })
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

        // First item: ctx: Type
        let _ctx_label: Ident = content.parse()?;
        content.parse::<Token![:]>()?;
        let ctx_type: Type = content.parse()?;
        // Optional trailing comma
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        }

        // Parse remaining items in any order
        let mut state_fields = None;
        let mut init = None;
        let mut lift = None;
        let mut invariant = None;
        let mut events = Vec::new();

        while !content.is_empty() {
            if content.peek(kw::state) {
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
            } else if content.peek(kw::event)
                || content.peek(kw::refined)
                || content.peek(kw::concrete)
                || content.peek(kw::convergent)
            {
                events.push(parse_event(&content)?);
            } else {
                return Err(content.error(
                    "expected 'state', 'init', 'lift', 'invariant', or event declaration",
                ));
            }
        }

        let name_span = name.span();
        Ok(MachineDecl {
            deadlock_free,
            name,
            refines,
            ctx_type,
            state_fields: state_fields.unwrap_or_default(),
            init: init.ok_or_else(|| syn::Error::new(name_span, "missing 'init' block"))?,
            lift,
            invariant,
            events,
        })
    }
}

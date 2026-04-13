use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{GenericArgument, PathArguments, Type};

use crate::parse::*;

/// Map a Verus spec type to an executable Rust type for the animate module.
///
/// `nat` / `int` become our `Nat` wrapper; `Seq` / `Set` / `Map` become the
/// `exec_types` wrappers (which expose the full spec API — `Seq::empty()`,
/// `.subrange()`, etc. — rather than a shallow `Vec` alias). Other types
/// (user structs, `bool`, `i32`, ...) pass through unchanged.
fn map_type_to_exec(ty: &Type) -> TokenStream {
    match ty {
        Type::Path(tp) => {
            if let Some(last_seg) = tp.path.segments.last() {
                let ident_str = last_seg.ident.to_string();
                match ident_str.as_str() {
                    "nat" | "int" => return quote! { verus_machine::exec_types::Nat },
                    "Seq" => {
                        let inner = generic_inner(&last_seg.arguments);
                        return quote! { verus_machine::exec_types::Seq<#(#inner),*> };
                    }
                    "Set" => {
                        let inner = generic_inner(&last_seg.arguments);
                        return quote! { ::std::collections::HashSet<#(#inner),*> };
                    }
                    "Map" => {
                        let inner = generic_inner(&last_seg.arguments);
                        return quote! { ::std::collections::HashMap<#(#inner),*> };
                    }
                    _ => {}
                }
            }
            quote! { #ty }
        }
        _ => quote! { #ty },
    }
}

fn generic_inner(args: &PathArguments) -> Vec<TokenStream> {
    if let PathArguments::AngleBracketed(ref args) = args {
        args.args
            .iter()
            .filter_map(|arg| {
                if let GenericArgument::Type(ref t) = arg {
                    Some(map_type_to_exec(t))
                } else {
                    None
                }
            })
            .collect()
    } else {
        Vec::new()
    }
}

/// Short human-readable tag for a type, used as the `ty_kind` in an input
/// prompt. `nat` → `"nat"`, `MyType` → `"MyType"`. Best-effort: for complex
/// types we just stringify the last segment of the path.
fn type_kind_label(ty: &Type) -> String {
    if let Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            return seg.ident.to_string();
        }
    }
    // Fallback to the full tokens — not pretty but unambiguous.
    quote! { #ty }.to_string()
}

/// Check if a type is `nat` or `int` (Verus ghost types).
fn is_ghost_numeric(ty: &verus_syn::Type) -> bool {
    if let verus_syn::Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            let s = seg.ident.to_string();
            return s == "nat" || s == "int";
        }
    }
    false
}

/// Transform a verus_syn expression tree into executable Rust tokens.
///
/// Key transformations:
/// - `&&&` prefix → `&&` infix chain
/// - `|||` prefix → `||` infix chain
/// - `expr as nat` / `expr as int` → strip the cast
/// - `..rest` in struct literals → `..rest.clone()`
/// - `seq![...]` → `Seq::from_vec(vec![...])` (vstd's `seq!` is a spec-only macro)
fn transform_expr(expr: &verus_syn::Expr) -> TokenStream {
    use verus_syn::Expr;

    match expr {
        Expr::BigAnd(ba) => {
            let exprs: Vec<_> = ba.exprs.iter().map(|e| transform_expr(&e.expr)).collect();
            if exprs.len() == 1 {
                exprs[0].clone()
            } else {
                let first = &exprs[0];
                let rest = &exprs[1..];
                quote! { (#first #(&& #rest)*) }
            }
        }
        Expr::BigOr(bo) => {
            let exprs: Vec<_> = bo.exprs.iter().map(|e| transform_expr(&e.expr)).collect();
            if exprs.len() == 1 {
                exprs[0].clone()
            } else {
                let first = &exprs[0];
                let rest = &exprs[1..];
                quote! { (#first #(|| #rest)*) }
            }
        }
        Expr::Cast(c) => {
            if is_ghost_numeric(&c.ty) {
                // Drop `as nat` / `as int` casts — Nat handles the semantics
                transform_expr(&c.expr)
            } else {
                let inner = transform_expr(&c.expr);
                let ty = &c.ty;
                quote! { #inner as #ty }
            }
        }
        Expr::Struct(s) => {
            let path = &s.path;
            let fields: Vec<_> = s
                .fields
                .iter()
                .map(|f| {
                    let member = &f.member;
                    let value = transform_expr(&f.expr);
                    if f.colon_token.is_some() {
                        quote! { #member: #value }
                    } else {
                        quote! { #member }
                    }
                })
                .collect();
            if let Some(ref rest) = s.rest {
                let rest_expr = transform_expr(rest);
                // Pre-clone the rest source so field values may consume parts
                // of it without aborting the final struct construction.
                quote! { {
                    let __rest = #rest_expr.clone();
                    #path { #(#fields,)* ..__rest }
                } }
            } else {
                quote! { #path { #(#fields,)* } }
            }
        }
        Expr::Binary(b) => {
            let left = transform_expr(&b.left);
            let right = transform_expr(&b.right);
            let op = &b.op;
            quote! { #left #op #right }
        }
        Expr::Paren(p) => {
            let inner = transform_expr(&p.expr);
            quote! { (#inner) }
        }
        Expr::MethodCall(m) => {
            let receiver = transform_expr(&m.receiver);
            let method = &m.method;
            let args: Vec<_> = m.args.iter().map(|a| transform_expr(a)).collect();
            if let Some(ref turbo) = m.turbofish {
                quote! { #receiver.#method::#turbo(#(#args),*) }
            } else {
                quote! { #receiver.#method(#(#args),*) }
            }
        }
        Expr::Field(f) => {
            let base = transform_expr(&f.base);
            let member = &f.member;
            quote! { #base.#member }
        }
        Expr::Call(c) => {
            let func = transform_expr(&c.func);
            let args: Vec<_> = c.args.iter().map(|a| transform_expr(a)).collect();
            quote! { #func(#(#args),*) }
        }
        Expr::Unary(u) => {
            let inner = transform_expr(&u.expr);
            let op = &u.op;
            quote! { #op #inner }
        }
        Expr::Block(b) => {
            let stmts: Vec<_> = b.block.stmts.iter().map(|s| transform_stmt(s)).collect();
            quote! { { #(#stmts)* } }
        }
        Expr::Reference(r) => {
            let inner = transform_expr(&r.expr);
            if r.mutability.is_some() {
                quote! { &mut #inner }
            } else {
                quote! { &#inner }
            }
        }
        Expr::If(i) => {
            let cond = transform_expr(&i.cond);
            let then_stmts: Vec<_> = i.then_branch.stmts.iter().map(|s| transform_stmt(s)).collect();
            let else_branch = i.else_branch.as_ref().map(|(_, expr)| {
                let e = transform_expr(expr);
                quote! { else #e }
            });
            quote! { if #cond { #(#then_stmts)* } #else_branch }
        }
        Expr::Index(i) => {
            let base = transform_expr(&i.expr);
            let idx = transform_expr(&i.index);
            // Route through `.at(i)` so bare integer literals like `seq[0]`
            // resolve unambiguously (direct `[]` indexing would need the
            // compiler to pick one of the many `Index<_>` impls on `Seq`).
            // `.at` returns `&T`; spec code wants a value, so clone.
            quote! { #base.at(#idx).clone() }
        }
        Expr::Group(g) => transform_expr(&g.expr),
        Expr::Macro(m) => {
            let mac = &m.mac;
            if let Some(last) = mac.path.segments.last() {
                let name = last.ident.to_string();
                if name == "seq" {
                    // `seq![a, b, c]` (vstd spec macro) → exec Seq built
                    // from a plain vec. The inner tokens are spliced through;
                    // if they contain Verus syntax this is a best-effort
                    // pass-through that will fail to compile rather than
                    // silently do the wrong thing.
                    let toks = &mac.tokens;
                    return quote! {
                        verus_machine::exec_types::Seq::from_vec(::std::vec![#toks])
                    };
                }
            }
            quote! { #expr }
        }
        // Paths, literals, and other standard expressions pass through.
        _ => quote! { #expr },
    }
}

fn transform_stmt(stmt: &verus_syn::Stmt) -> TokenStream {
    match stmt {
        verus_syn::Stmt::Expr(expr, semi) => {
            let transformed = transform_expr(expr);
            if semi.is_some() {
                quote! { #transformed; }
            } else {
                transformed
            }
        }
        verus_syn::Stmt::Local(local) => {
            let pat = &local.pat;
            if let Some(ref init) = local.init {
                let init_expr = transform_expr(&init.expr);
                quote! { let #pat = #init_expr; }
            } else {
                quote! { let #pat; }
            }
        }
        _ => quote! { #stmt },
    }
}

/// Parse a TokenStream body as a verus_syn expression and transform it to executable Rust.
fn transform_body(body: &TokenStream) -> TokenStream {
    match verus_syn::parse2::<verus_syn::Expr>(body.clone()) {
        Ok(expr) => transform_expr(&expr),
        Err(_) => {
            let block_tokens = quote! { { #body } };
            match verus_syn::parse2::<verus_syn::Expr>(block_tokens) {
                Ok(expr) => transform_expr(&expr),
                Err(_) => {
                    quote! { compile_error!("animate: could not parse body as verus expression") }
                }
            }
        }
    }
}

/// Build the exec context type path from a spec context type.
///
/// For a path like `abs::Ctx`, produces `abs::animate::Ctx` — the exec mirror
/// lives inside the `animate` submodule of the declaring machine's module.
fn exec_ctx_type(spec_type: &Type) -> TokenStream {
    match spec_type {
        Type::Path(tp) => {
            let mut segments: Vec<_> = tp.path.segments.iter().collect();
            if segments.len() >= 2 {
                let last = segments.pop().unwrap();
                let prefix: Vec<_> = segments.iter().map(|s| quote! { #s }).collect();
                let type_name = &last.ident;
                quote! { #(#prefix::)* animate::#type_name }
            } else {
                let ident = &segments[0].ident;
                quote! { #ident }
            }
        }
        _ => quote! { #spec_type },
    }
}

/// Check if a syn::Type is `nat` or `int`.
fn is_nat_field(ty: &Type) -> bool {
    if let Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            let s = seg.ident.to_string();
            return s == "nat" || s == "int";
        }
    }
    false
}

pub fn expand_animate(decl: &MachineDecl) -> TokenStream {
    let name = &decl.name;
    let name_str = name.to_string();
    let event_enum_name = format_ident!("{}Event", name);

    // Determine exec ctx type and whether we need to generate it
    let (exec_ctx, exec_ctx_struct) = match &decl.ctx {
        CtxDecl::External(ty) => (exec_ctx_type(ty), quote! {}),
        CtxDecl::Inline { fields, .. } => {
            let ctx_type: TokenStream = quote! { Ctx };
            let exec_fields: Vec<_> = fields
                .iter()
                .map(|f| {
                    let fname = &f.name;
                    let exec_ty = map_type_to_exec(&f.ty);
                    quote! { pub #fname: #exec_ty }
                })
                .collect();
            let struct_def = quote! {
                #[derive(Debug, Clone, PartialEq)]
                pub struct Ctx {
                    #(#exec_fields,)*
                }
            };
            (ctx_type, struct_def)
        }
    };

    // --- State struct fields with executable types ---
    let exec_fields: Vec<_> = decl
        .state_fields
        .iter()
        .map(|f| {
            let fname = &f.name;
            let exec_ty = map_type_to_exec(&f.ty);
            quote! { pub #fname: #exec_ty }
        })
        .collect();

    // --- Display impl ---
    let display_fields: Vec<_> = decl
        .state_fields
        .iter()
        .map(|f| {
            let fname = &f.name;
            let fname_str = fname.to_string();
            quote! { .field(#fname_str, &self.#fname) }
        })
        .collect();

    // --- Event enum ---
    // Each event becomes one variant; events with an `Input` carry that input
    // as the sole payload so menu selection / random stepping / construct_event
    // all get a uniform unpack point.
    let event_variants: Vec<TokenStream> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            if let Some(ref param) = evt.input {
                let ty = map_type_to_exec(&param.ty);
                quote! { #ename(#ty) }
            } else {
                quote! { #ename }
            }
        })
        .collect();

    // --- Display impl for event enum ---
    let event_display_arms: Vec<TokenStream> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let ename_str = ename.to_string();
            if evt.input.is_some() {
                quote! { Self::#ename(__x) => write!(f, "{}({})", #ename_str, __x) }
            } else {
                quote! { Self::#ename => write!(f, "{}", #ename_str) }
            }
        })
        .collect();

    // --- Init body ---
    let init_body = {
        let init_tokens = &decl.init.body;
        let struct_tokens = quote! { #name { #init_tokens } };
        match verus_syn::parse2::<verus_syn::Expr>(struct_tokens) {
            Ok(verus_syn::Expr::Struct(s)) => {
                let fields: Vec<_> = s
                    .fields
                    .iter()
                    .map(|f| {
                        let member = &f.member;
                        let value = transform_expr(&f.expr);
                        // Wrap nat/int literals with `.into()` — user writes
                        // `cars: 0` and we need `cars: 0i32.into()` to hit Nat.
                        let member_name = quote! { #member }.to_string();
                        let field_is_nat = decl.state_fields.iter().any(|sf| {
                            sf.name == member_name && is_nat_field(&sf.ty)
                        });
                        if field_is_nat {
                            quote! { #member: (#value).into() }
                        } else {
                            quote! { #member: #value }
                        }
                    })
                    .collect();
                quote! { #name { #(#fields,)* } }
            }
            _ => quote! { #name { #init_tokens } },
        }
    };

    // --- Guard / action match arms ---
    // Destructure the variant payload so the input param name is bound inside
    // the user's body. We clone the event once up front (cheap — inputs are
    // small) so the body sees owned values even in `guard`.
    let guard_arms: Vec<_> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let guard_body = transform_body(&evt.guard.body);
            let ctx_name = &evt.guard.ctx_name;
            let state_name = &evt.guard.state_name;
            let pattern = if let Some(ref param) = evt.input {
                let pname = &param.name;
                quote! { #event_enum_name::#ename(#pname) }
            } else {
                quote! { #event_enum_name::#ename }
            };
            quote! {
                #pattern => {
                    let #ctx_name = ctx;
                    let #state_name = state;
                    #guard_body
                }
            }
        })
        .collect();

    let action_arms: Vec<_> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let action_body = transform_body(&evt.action.body);
            let ctx_name = &evt.action.ctx_name;
            let state_name = &evt.action.state_name;
            let pattern = if let Some(ref param) = evt.input {
                let pname = &param.name;
                quote! { #event_enum_name::#ename(#pname) }
            } else {
                quote! { #event_enum_name::#ename }
            };
            quote! {
                #pattern => {
                    let #ctx_name = ctx.clone();
                    let #state_name = state.clone();
                    #action_body
                }
            }
        })
        .collect();

    // --- Output match arms ---
    // For events with an `output` body, evaluate it on the pre-action state
    // and format with Display. Events without an output contribute a `None`.
    let output_arms: Vec<_> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let pattern = if let Some(ref param) = evt.input {
                let pname = &param.name;
                quote! { #event_enum_name::#ename(#pname) }
            } else {
                quote! { #event_enum_name::#ename }
            };
            if let Some(ref out) = evt.output {
                let out_body = transform_body(&out.body);
                let ctx_name = &out.ctx_name;
                let state_name = &out.state_name;
                quote! {
                    #pattern => {
                        let #ctx_name = ctx.clone();
                        let #state_name = state.clone();
                        let __out = { #out_body };
                        ::std::option::Option::Some(format!("{}", __out))
                    }
                }
            } else {
                quote! {
                    #pattern => ::std::option::Option::None,
                }
            }
        })
        .collect();

    // --- event_menu, construct_event, random_event ---
    let menu_entries: Vec<TokenStream> = decl
        .events
        .iter()
        .map(|evt| {
            let ename_str = evt.name.to_string();
            if let Some(ref param) = evt.input {
                let pname_str = param.name.to_string();
                let ty_label = type_kind_label(&param.ty);
                quote! {
                    verus_machine::animate::EventSpec {
                        name: #ename_str,
                        inputs: ::std::vec![
                            verus_machine::animate::InputSpec {
                                name: #pname_str,
                                ty_kind: #ty_label,
                            }
                        ],
                    }
                }
            } else {
                quote! {
                    verus_machine::animate::EventSpec {
                        name: #ename_str,
                        inputs: ::std::vec![],
                    }
                }
            }
        })
        .collect();

    let construct_arms: Vec<TokenStream> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let ename_str = ename.to_string();
            if let Some(ref param) = evt.input {
                let ty = map_type_to_exec(&param.ty);
                quote! {
                    #ename_str => {
                        if inputs.len() != 1 {
                            return Err(format!(
                                "{} expects 1 input, got {}",
                                #ename_str,
                                inputs.len()
                            ));
                        }
                        let v: #ty =
                            <#ty as verus_machine::exec_types::ParseInput>::parse_input(&inputs[0])?;
                        Ok(#event_enum_name::#ename(v))
                    }
                }
            } else {
                quote! {
                    #ename_str => {
                        if !inputs.is_empty() {
                            return Err(format!(
                                "{} expects no inputs, got {}",
                                #ename_str,
                                inputs.len()
                            ));
                        }
                        Ok(#event_enum_name::#ename)
                    }
                }
            }
        })
        .collect();

    let n_events = decl.events.len();
    let random_arms: Vec<TokenStream> = decl
        .events
        .iter()
        .enumerate()
        .map(|(i, evt)| {
            let ename = &evt.name;
            let idx = i as u32;
            if let Some(ref param) = evt.input {
                let ty = map_type_to_exec(&param.ty);
                quote! {
                    #idx => #event_enum_name::#ename(
                        <#ty as verus_machine::exec_types::Sample>::sample(rng)
                    ),
                }
            } else {
                quote! {
                    #idx => #event_enum_name::#ename,
                }
            }
        })
        .collect();

    // --- Auxiliary function exec impls ---
    let aux_fn_exec_methods: Vec<_> = decl
        .aux_fns
        .iter()
        .map(|f| {
            let fn_name = &f.name;
            let state_name = &f.state_name;
            let exec_ret_type = map_type_to_exec(&f.ret_type);
            let exec_body = transform_body(&f.body);
            quote! {
                pub fn #fn_name(&self) -> #exec_ret_type {
                    let #state_name = self.clone();
                    #exec_body
                }
            }
        })
        .collect();

    let aux_fn_exec_impl = if aux_fn_exec_methods.is_empty() {
        quote! {}
    } else {
        quote! {
            impl #name {
                #(#aux_fn_exec_methods)*
            }
        }
    };

    let n_events_lit = n_events as u32;
    // If the machine has zero events, random_event can't produce anything.
    // Generate a stub that panics — callers shouldn't reach it, but the type
    // system needs the method to exist.
    let random_event_body = if n_events == 0 {
        quote! {
            let _ = rng;
            panic!("random_event called on a machine with no events");
        }
    } else {
        quote! {
            let __n = rand::Rng::gen_range(rng, 0u32..#n_events_lit);
            match __n {
                #(#random_arms)*
                _ => unreachable!(),
            }
        }
    };

    quote! {
        #[cfg(not(verus_only))]
        #[allow(dead_code, unused_variables, unused_imports)]
        pub mod animate {
            use super::*;
            // Shadow any spec-level Seq/Nat brought in via `use super::*;` so
            // bodies like `Seq::empty()` / `state.size + 1` resolve to our
            // exec types.
            use verus_machine::exec_types::{IntoIdx, Nat, Seq};

            #exec_ctx_struct

            #[derive(Debug, Clone, PartialEq)]
            pub struct #name {
                #(#exec_fields,)*
            }

            impl ::std::fmt::Display for #name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                    f.debug_struct(#name_str)
                        #(#display_fields)*
                        .finish()
                }
            }

            #aux_fn_exec_impl

            #[derive(Debug, Clone, PartialEq)]
            pub enum #event_enum_name {
                #(#event_variants,)*
            }

            impl ::std::fmt::Display for #event_enum_name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                    match self {
                        #(#event_display_arms,)*
                    }
                }
            }

            impl verus_machine::animate::Animate for #name {
                type Ctx = #exec_ctx;
                type Event = #event_enum_name;

                fn init(ctx: &Self::Ctx) -> Self {
                    let ctx = ctx;
                    #init_body
                }

                fn event_menu() -> ::std::vec::Vec<verus_machine::animate::EventSpec> {
                    ::std::vec![#(#menu_entries,)*]
                }

                fn construct_event(
                    name: &str,
                    inputs: &[::std::string::String],
                ) -> ::std::result::Result<Self::Event, ::std::string::String> {
                    match name {
                        #(#construct_arms)*
                        other => Err(format!("unknown event {:?}", other)),
                    }
                }

                fn random_event<R: rand::Rng + ?Sized>(rng: &mut R) -> Self::Event {
                    #random_event_body
                }

                fn guard(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> bool {
                    let event = event.clone();
                    match event {
                        #(#guard_arms)*
                    }
                }

                fn action(ctx: &Self::Ctx, state: &Self, event: &Self::Event) -> Self {
                    let event = event.clone();
                    match event {
                        #(#action_arms)*
                    }
                }

                fn output(
                    ctx: &Self::Ctx,
                    state: &Self,
                    event: &Self::Event,
                ) -> ::std::option::Option<::std::string::String> {
                    let event = event.clone();
                    match event {
                        #(#output_arms)*
                    }
                }
            }
        }
    }
}

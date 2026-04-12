use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{GenericArgument, Ident, PathArguments, Type};

use crate::parse::*;

/// Map a Verus spec type to an executable Rust type for the animate module.
fn map_type_to_exec(ty: &Type) -> TokenStream {
    match ty {
        Type::Path(tp) => {
            if let Some(last_seg) = tp.path.segments.last() {
                let ident_str = last_seg.ident.to_string();
                match ident_str.as_str() {
                    "nat" | "int" => return quote! { verus_machine::exec_types::Nat },
                    "Seq" => {
                        if let PathArguments::AngleBracketed(ref args) = last_seg.arguments {
                            let inner: Vec<_> = args
                                .args
                                .iter()
                                .filter_map(|arg| {
                                    if let GenericArgument::Type(ref t) = arg {
                                        Some(map_type_to_exec(t))
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            return quote! { Vec<#(#inner),*> };
                        }
                        return quote! { Vec };
                    }
                    "Set" => {
                        if let PathArguments::AngleBracketed(ref args) = last_seg.arguments {
                            let inner: Vec<_> = args
                                .args
                                .iter()
                                .filter_map(|arg| {
                                    if let GenericArgument::Type(ref t) = arg {
                                        Some(map_type_to_exec(t))
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            return quote! { ::std::collections::HashSet<#(#inner),*> };
                        }
                        return quote! { ::std::collections::HashSet };
                    }
                    "Map" => {
                        if let PathArguments::AngleBracketed(ref args) = last_seg.arguments {
                            let inner: Vec<_> = args
                                .args
                                .iter()
                                .filter_map(|arg| {
                                    if let GenericArgument::Type(ref t) = arg {
                                        Some(map_type_to_exec(t))
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            return quote! { ::std::collections::HashMap<#(#inner),*> };
                        }
                        return quote! { ::std::collections::HashMap };
                    }
                    _ => {}
                }
            }
            quote! { #ty }
        }
        _ => quote! { #ty },
    }
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
                        // Shorthand like `Foo { x }` → `Foo { x }`
                        quote! { #member }
                    }
                })
                .collect();
            if let Some(ref rest) = s.rest {
                let rest_expr = transform_expr(rest);
                // Pre-clone the rest source to avoid partial move issues:
                // field values may consume (move) individual fields, which would
                // prevent cloning the whole struct afterwards.
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
        Expr::Group(g) => {
            transform_expr(&g.expr)
        }
        // For all other expression types, use verus_syn's ToTokens.
        // This covers paths, literals, and standard Rust expressions
        // that don't contain Verus-specific syntax.
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
            // let bindings: transform the init expression if present
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
    // Try parsing the body as a verus_syn expression
    match verus_syn::parse2::<verus_syn::Expr>(body.clone()) {
        Ok(expr) => transform_expr(&expr),
        Err(_) => {
            // If parsing as a single expression fails, try as a block
            let block_tokens = quote! { { #body } };
            match verus_syn::parse2::<verus_syn::Expr>(block_tokens) {
                Ok(expr) => transform_expr(&expr),
                Err(_) => {
                    // Fallback: emit as-is with a compile warning
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
                // e.g. abs::Ctx → abs::animate::Ctx
                let last = segments.pop().unwrap();
                let prefix: Vec<_> = segments.iter().map(|s| quote! { #s }).collect();
                let type_name = &last.ident;
                quote! { #(#prefix::)* animate::#type_name }
            } else {
                // Single-segment path (e.g. just `Ctx`) — assume it's in the
                // same module; animate::Ctx will shadow via `use super::*`
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
    let event_names: Vec<&Ident> = decl.events.iter().map(|e| &e.name).collect();
    let event_name_strs: Vec<String> = decl.events.iter().map(|e| e.name.to_string()).collect();

    // --- Init body ---
    // Parse init body field values and wrap nat-typed fields with .into()
    let init_body = {
        let init_tokens = &decl.init.body;
        // Wrap as a struct expression so verus_syn can parse it
        let struct_tokens = quote! { #name { #init_tokens } };
        match verus_syn::parse2::<verus_syn::Expr>(struct_tokens) {
            Ok(verus_syn::Expr::Struct(s)) => {
                let fields: Vec<_> = s
                    .fields
                    .iter()
                    .map(|f| {
                        let member = &f.member;
                        let value = transform_expr(&f.expr);
                        // Check if this field is nat/int type and wrap with .into()
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
            _ => {
                // Fallback: just use the raw tokens
                quote! { #name { #init_tokens } }
            }
        }
    };

    // --- Guard match arms ---
    let guard_arms: Vec<_> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let guard_body = transform_body(&evt.guard.body);
            let ctx_name = &evt.guard.ctx_name;
            let state_name = &evt.guard.state_name;
            quote! {
                #event_enum_name::#ename => {
                    let #ctx_name = ctx;
                    let #state_name = state;
                    #guard_body
                }
            }
        })
        .collect();

    // --- Action match arms ---
    // Clone state so field accesses are on owned values (Nat isn't Copy).
    let action_arms: Vec<_> = decl
        .events
        .iter()
        .map(|evt| {
            let ename = &evt.name;
            let action_body = transform_body(&evt.action.body);
            let ctx_name = &evt.action.ctx_name;
            let state_name = &evt.action.state_name;
            quote! {
                #event_enum_name::#ename => {
                    let #ctx_name = ctx.clone();
                    let #state_name = state.clone();
                    #action_body
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

    quote! {
        #[cfg(not(verus_only))]
        #[allow(dead_code, unused_variables)]
        pub mod animate {
            use super::*;

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

            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum #event_enum_name {
                #(#event_names,)*
            }

            impl ::std::fmt::Display for #event_enum_name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                    match self {
                        #(Self::#event_names => write!(f, #event_name_strs),)*
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

                fn events() -> Vec<Self::Event> {
                    vec![#(#event_enum_name::#event_names,)*]
                }

                fn guard(ctx: &Self::Ctx, state: &Self, event: Self::Event) -> bool {
                    match event {
                        #(#guard_arms)*
                    }
                }

                fn action(ctx: &Self::Ctx, state: &Self, event: Self::Event) -> Self {
                    match event {
                        #(#action_arms)*
                    }
                }
            }
        }
    }
}

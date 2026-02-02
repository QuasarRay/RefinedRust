extern crate syn;
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, parse_quote, Item, ItemFn};
use proc_macro2::TokenStream as TokenStream2;

use syn::{
    visit_mut::{self, VisitMut},
    Expr, ExprWhile, ExprForLoop, ExprLoop, Stmt, Attribute,
};


// TODO: questions to figure out:
// - Fix params and other attributes which can not only occur on functions but also loops.
// - How do I get stuff to work on closures?

#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    LoopRewriter.visit_item_fn_mut(&mut func);

    quote::quote!(#func).into()
}


#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::requires(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::requires(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::ensures(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::ensures(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn returns(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::returns(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::returns(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn params(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::params(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::params(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn exists(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::exists(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::exists(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn args(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::args(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::args(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn observe(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    // 1. Re-emit #[rr::observe(attr)]
    let attr2: TokenStream2 = attr.into();
    let rr_attr: Attribute = parse_quote!(#[rr::observe(#attr2)]);
    func.attrs.push(rr_attr);

    // 2. Rewrite loops in the function body
    let mut rewriter = LoopRewriter;
    rewriter.visit_block_mut(&mut func.block);

    TokenStream::from(quote!(#func))
}

#[proc_macro_attribute]
pub fn inv(args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input item
    let input = parse_macro_input!(input as Item);

    // Reconstruct the args as TokenStream
    let args = TokenStream2::from(args);

    // Generate the output: just attach #[rr::inv(...)] to the original item
    let output = quote! {
        #[rr::inv(#args)]
        #input
    };

    output.into()
}


struct LoopRewriter;

impl VisitMut for LoopRewriter {
    fn visit_expr_mut(&mut self, i: &mut Expr) {
        let expr = &mut *i;
        visit_mut::visit_expr_mut(self, expr);

        if let Expr::While(expr_while) = expr {
            rewrite_while(expr_while);
        }
        else if let Expr::ForLoop(expr_for) = expr {
            rewrite_for(expr_for);
        }
        else if let Expr::Loop(expr_loop) = expr {
            rewrite_loop(expr_loop);
        }
    }
}

fn is_rr_ignore_closure(stmt: &syn::Stmt) -> bool {
    let syn::Stmt::Expr(expr, _) = stmt else {
        return false;
    };

    let syn::Expr::Closure(closure) = expr else {
        return false;
    };

    closure.attrs.iter().any(|attr| {
        let path = attr.path();
        let mut segments = path.segments.iter();

        matches!(
            (segments.next(), segments.next()),
            (Some(first), Some(second))
                if first.ident == "rr" && second.ident == "ignore"
        )
    })
}

fn extract_rr_attrs(attrs: &mut Vec<Attribute>) -> Vec<Attribute> {
    // Extract rr::* attributes
    let mut rr_attrs = Vec::new();
    attrs.retain(|attr| {
        let is_rr = attr.path().segments.first().is_some_and(|s| s.ident == "rr");
        if is_rr {
            rr_attrs.push(attr.clone());
            false
        } else {
            true
        }
    });
    rr_attrs
}

fn rewrite_while(expr_while: &mut ExprWhile) {
    if expr_while
        .body
        .stmts
        .first()
        .is_some_and(is_rr_ignore_closure)
    {
        return;
    }

    let mut rr_attrs = extract_rr_attrs(&mut expr_while.attrs);
    if rr_attrs.is_empty() {
        return;
    }

    // Add #[rr::ignore]
    let span = expr_while.while_token.span;
    rr_attrs.push(syn::parse_quote!(#[rr::ignore]));
    rr_attrs.push(syn::parse_quote!(#[allow(unused)]));

    // Build closure expression
    let closure_stmt: Stmt = syn::parse_quote_spanned! {span=>
        #(#rr_attrs)*
        || {};
    };

    // Insert at top of loop body
    expr_while.body.stmts.insert(0, closure_stmt);
}

fn rewrite_for(expr_for: &mut ExprForLoop) {
    if expr_for
        .body
        .stmts
        .first()
        .is_some_and(is_rr_ignore_closure)
    {
        return;
    }

    let mut rr_attrs = extract_rr_attrs(&mut expr_for.attrs);
    if rr_attrs.is_empty() {
        return;
    }

    // Add #[rr::ignore]
    let span = expr_for.for_token.span;
    rr_attrs.push(syn::parse_quote!(#[rr::ignore]));
    rr_attrs.push(syn::parse_quote!(#[allow(unused)]));

    // Build closure expression
    let closure_stmt: Stmt = syn::parse_quote_spanned! {span=>
        #(#rr_attrs)*
        || {};
    };

    // Insert at top of loop body
    expr_for.body.stmts.insert(0, closure_stmt);
}

fn rewrite_loop(expr_loop: &mut ExprLoop) {
    if expr_loop
        .body
        .stmts
        .first()
        .is_some_and(is_rr_ignore_closure)
    {
        return;
    }

    let mut rr_attrs = extract_rr_attrs(&mut expr_loop.attrs);
    if rr_attrs.is_empty() {
        return;
    }

    // Add #[rr::ignore]
    let span = expr_loop.loop_token.span;
    rr_attrs.push(syn::parse_quote!(#[rr::ignore]));
    rr_attrs.push(syn::parse_quote!(#[allow(unused)]));

    // Build closure expression
    let closure_stmt: Stmt = syn::parse_quote_spanned! {span=>
        #(#rr_attrs)*
        || {};
    };

    // Insert at top of loop body
    expr_loop.body.stmts.insert(0, closure_stmt);
}

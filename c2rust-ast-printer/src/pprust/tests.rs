use super::*;

use rustc_ast::ast;
use rustc_span::with_default_session_globals;
use rustc_span::symbol;

fn fun_to_string(
    decl: &ast::FnDecl, header: ast::FnHeader, name: symbol::Ident, generics: &ast::Generics
) -> String {
    let vis = ast::Visibility {
        kind: ast::VisibilityKind::Inherited,
        span: rustc_span::DUMMY_SP,
        tokens: None,
    };
    to_string(|s| {
        s.head("");
        s.print_fn(decl, header, Some(name), generics, &vis);
        s.end(); // Close the head box.
        s.end(); // Close the outer box.
    })
}

fn variant_to_string(var: &ast::Variant) -> String {
    to_string(|s| s.print_variant(var))
}

#[test]
fn test_fun_to_string() {
    with_default_session_globals(|| {
        let abba_ident = symbol::Ident::from_str("abba");

        let decl = ast::FnDecl {
            inputs: Vec::new(),
            output: ast::FnRetTy::Default(rustc_span::DUMMY_SP),
        };
        let generics = ast::Generics::default();
        assert_eq!(
            fun_to_string(
                &decl,
                ast::FnHeader::default(),
                abba_ident,
                &generics
            ),
            "fn abba()"
        );
    })
}

#[test]
fn test_variant_to_string() {
    with_default_session_globals(|| {
        let ident = symbol::Ident::from_str("principal_skinner");
        let vis = ast::Visibility {
            kind: ast::VisibilityKind::Inherited,
            span: rustc_span::DUMMY_SP,
            tokens: None,
        };

        let var = ast::Variant {
            ident,
            vis,
            attrs: Vec::new(),
            id: ast::DUMMY_NODE_ID,
            data: ast::VariantData::Unit(ast::DUMMY_NODE_ID),
            disr_expr: None,
            span: rustc_span::DUMMY_SP,
            is_placeholder: false,
        };

        let varstr = variant_to_string(&var);
        assert_eq!(varstr, "principal_skinner");
    })
}

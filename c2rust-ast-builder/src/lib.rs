#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_ast;
extern crate rustc_span;
extern crate rustc_hir;
extern crate rustc_data_structures;

mod builder;
pub use builder::{mk, Builder, Make};

mod into_symbol;
pub use into_symbol::IntoSymbol;

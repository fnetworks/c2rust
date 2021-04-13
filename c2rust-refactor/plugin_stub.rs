//! A generic wrapper for building parts of `c2rust-refactor` as a plugin.

#![feature(
    i128_type,
    rustc_private,
    trace_macros,
)]
extern crate arena;
extern crate ena;
extern crate libc;
extern crate diff;
#[macro_use] extern crate json;
#[macro_use] extern crate log;
extern crate regex;
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_metadata;
extern crate rustc_resolve;
extern crate rustc_trans;
extern crate syntax;
extern crate syntax_ext;
extern crate rustc_span;

#[macro_use] extern crate c2rust_refactor;
pub use c2rust_refactor::*;


fn mk<T: transform::Transform + 'static>(t: T) -> Box<command::Command> {
    Box::new(transform::TransformCommand(t))
}

// Adjust these lines to control what part of `c2rust-refactor` gets built.
//#[path="src/analysis/mod.rs"]
#[path="src/transform/retype.rs"]
mod plugin;
//use self::plugin as analysis;

#[no_mangle]
pub fn register_commands(reg: &mut command::Registry) {
    plugin::register_commands(reg);
}

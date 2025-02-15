//! Functions for rewriting sequences of stmts or items, using `Cursor<T>`.
use std::mem;
use rustc_ast::ast::{Block, Item, ItemKind, ModKind, Stmt};
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_ast::ptr::P;

use crate::ast_manip::MutVisit;
use crate::util::cursor::Cursor;

struct BlockFolder<F: FnMut(&mut Cursor<Stmt>)> {
    f: F,
}

impl<F: FnMut(&mut Cursor<Stmt>)> MutVisitor for BlockFolder<F> {
    fn visit_block(&mut self, b: &mut P<Block>) {
        let stmts = mem::replace(&mut b.stmts, vec![]);
        let mut stmt_cursor = Cursor::from_vec(stmts);
        (self.f)(&mut stmt_cursor);
        b.stmts = stmt_cursor.into_vec();
        mut_visit::noop_visit_block(b, self)
    }
}

/// Rewrite every block by manipulating a `Cursor` for the `Stmt`s inside.
pub fn fold_blocks<T, F>(target: &mut T, callback: F)
where
    T: MutVisit,
    F: FnMut(&mut Cursor<Stmt>),
{
    target.visit(&mut BlockFolder { f: callback })
}

struct ModuleFolder<F: FnMut(&mut Cursor<P<Item>>)> {
    f: F,
}

impl<F: FnMut(&mut Cursor<P<Item>>)> MutVisitor for ModuleFolder<F> {
    fn visit_item_kind(&mut self, m: &mut ItemKind) {
        match m {
            ItemKind::Mod(_unsafety, mod_kind) => match mod_kind {
                ModKind::Loaded(ref mut items, _inline, _inner_span) => {
                    let items = mem::replace(items, vec![]);
                    let mut curs = Cursor::from_vec(items);
                    (self.f)(&mut curs);
                    *items = curs.into_vec();
                }
            }
        }
        mut_visit::noop_visit_item_kind(m, self)
    }
}

/// Rewrite every module by manipulating a `Cursor` for the `Item`s inside.
pub fn fold_modules<T, F>(target: &mut T, callback: F)
where
    T: MutVisit,
    F: FnMut(&mut Cursor<P<Item>>),
{
    target.visit(&mut ModuleFolder { f: callback })
}

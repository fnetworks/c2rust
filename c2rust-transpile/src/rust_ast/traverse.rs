use rustc_ast::ast::*;
use rustc_ast::ptr;

/// Traverse the AST in pre-order, which also happens to be the order of subtrees in the
/// pretty-printed output.
pub trait Traversal: Sized {
    fn traverse_stmt(&mut self, s: Stmt) -> Stmt {
        traverse_stmt_def(self, s)
    }

    fn traverse_expr(&mut self, s: Expr) -> Expr {
        traverse_expr_def(self, s)
    }

    /*
    fn traverse_trait_item(&mut self, ti: TraitItem) -> TraitItem {
        traverse_trait_item_def(self, ti)
    }

    fn traverse_impl_item(&mut self, ii: ImplItem) -> ImplItem {
        traverse_impl_item_def(self, ii)
    }*/

    fn traverse_assoc_item(&mut self, ai: AssocItem) -> AssocItem {
        traverse_assoc_item_def(self, ai)
    }

    fn traverse_block(&mut self, b: Block) -> Block {
        traverse_block_def(self, b)
    }

    fn traverse_local(&mut self, l: Local) -> Local {
        traverse_local_def(self, l)
    }

    fn traverse_arm(&mut self, a: Arm) -> Arm {
        traverse_arm_def(self, a)
    }

    fn traverse_field(&mut self, f: ExprField) -> ExprField {
        traverse_field_def(self, f)
    }

    fn traverse_mod(&mut self, m: ModKind) -> ModKind {
        traverse_mod_def(self, m)
    }

    fn traverse_foreign_mod(&mut self, m: ForeignMod) -> ForeignMod {
        traverse_foreign_mod_def(self, m)
    }

    fn traverse_item(&mut self, i: Item) -> Item {
        traverse_item_def(self, i)
    }

    fn traverse_foreign_item(&mut self, i: ForeignItem) -> ForeignItem {
        i
    }

    fn traverse_struct_rest(&mut self, r: StructRest) -> StructRest {
        traverse_struct_rest_def(self, r)
    }
}

/// Apply a `Traversal` to an AST node.
trait Traversable {
    fn traverse<T: Traversal>(self, t: &mut T) -> Self;
}

macro_rules! traversable_impl {
    ( $traversable_ty:ty, $method_name:ident ) => {
        impl Traversable for $traversable_ty {
            fn traverse<T: Traversal>(self, t: &mut T) -> Self {
                t.$method_name(self)
            }
        }
    };
}

traversable_impl!(Stmt, traverse_stmt);
traversable_impl!(Expr, traverse_expr);
//traversable_impl!(TraitItem, traverse_trait_item);
//traversable_impl!(ImplItem, traverse_impl_item);
traversable_impl!(AssocItem, traverse_assoc_item);
traversable_impl!(Block, traverse_block);
traversable_impl!(Local, traverse_local);
traversable_impl!(Arm, traverse_arm);
traversable_impl!(ExprField, traverse_field);
traversable_impl!(ModKind, traverse_mod);
traversable_impl!(ForeignMod, traverse_foreign_mod);
traversable_impl!(Item, traverse_item);
traversable_impl!(ForeignItem, traverse_foreign_item);
traversable_impl!(StructRest, traverse_struct_rest);

impl<A: Traversable> Traversable for Vec<A> {
    fn traverse<T: Traversal>(self, t: &mut T) -> Self {
        self.into_iter().map(|x| x.traverse(t)).collect()
    }
}

impl<A: Traversable> Traversable for Option<A> {
    fn traverse<T: Traversal>(self, t: &mut T) -> Self {
        self.map(|x| x.traverse(t))
    }
}

impl<A: Traversable + 'static> Traversable for ptr::P<A> {
    fn traverse<T: Traversal>(self, t: &mut T) -> Self {
        self.map(|x| x.traverse(t))
    }
}

pub fn traverse_stmt_def<W: Traversal>(walk: &mut W, mut s: Stmt) -> Stmt {
    s.kind = match s.kind {
        StmtKind::Local(p_local) => StmtKind::Local(p_local.traverse(walk)),
        StmtKind::Item(p_item) => StmtKind::Item(p_item.traverse(walk)),
        StmtKind::Expr(p_expr) => StmtKind::Expr(p_expr.traverse(walk)),
        StmtKind::Semi(p_expr) => StmtKind::Semi(p_expr.traverse(walk)),
        StmtKind::MacCall(m) => StmtKind::MacCall(m),
        StmtKind::Empty => StmtKind::Empty,
    };
    s
}

pub fn traverse_expr_def<W: Traversal>(walk: &mut W, mut e: Expr) -> Expr {
    e.kind = match e.kind {
        ExprKind::Box(p_expr) => ExprKind::Box(p_expr.map(|expr| walk.traverse_expr(expr))),
        ExprKind::Array(elems) => ExprKind::Array(elems.traverse(walk)),
        ExprKind::Call(func, args) => ExprKind::Call(func.traverse(walk), args.traverse(walk)),
        ExprKind::MethodCall(meth, args, span) => ExprKind::MethodCall(meth, args.traverse(walk), span),
        ExprKind::Tup(elems) => ExprKind::Tup(elems.traverse(walk)),
        ExprKind::Binary(op, lhs, rhs) => {
            ExprKind::Binary(op, lhs.traverse(walk), rhs.traverse(walk))
        }
        ExprKind::Unary(op, arg) => ExprKind::Unary(op, arg.traverse(walk)),
        ExprKind::Cast(arg, t) => ExprKind::Cast(arg.traverse(walk), t),
        ExprKind::Type(arg, t) => ExprKind::Type(arg.traverse(walk), t),
        ExprKind::Let(pat, e) => ExprKind::Let(pat, e.traverse(walk)),
        ExprKind::If(cond, thn, els) => {
            ExprKind::If(cond.traverse(walk), thn.traverse(walk), els.traverse(walk))
        }
        ExprKind::While(cond, block, lbl) => {
            ExprKind::While(cond.traverse(walk), block.traverse(walk), lbl)
        }
        ExprKind::ForLoop(pat, cond, block, lbl) => {
            ExprKind::ForLoop(pat, cond.traverse(walk), block.traverse(walk), lbl)
        }
        ExprKind::Loop(block, lbl) => ExprKind::Loop(block.traverse(walk), lbl),
        ExprKind::Match(cond, arm) => ExprKind::Match(cond.traverse(walk), arm.traverse(walk)),
        ExprKind::Closure(cap, isasync, mov, fn_decl, expr, s) => {
            ExprKind::Closure(cap, isasync, mov, fn_decl, expr.traverse(walk), s)
        }
        ExprKind::Block(block, lbl) => ExprKind::Block(block.traverse(walk), lbl),
        ExprKind::Assign(lhs, rhs, span) => ExprKind::Assign(lhs.traverse(walk), rhs.traverse(walk), span),
        ExprKind::AssignOp(op, lhs, rhs) => {
            ExprKind::AssignOp(op, lhs.traverse(walk), rhs.traverse(walk))
        }
        ExprKind::Field(expr, f) => ExprKind::Field(expr.traverse(walk), f),
        ExprKind::Index(lhs, rhs) => ExprKind::Index(lhs.traverse(walk), rhs.traverse(walk)),
        ExprKind::Range(lhs, rhs, l) => ExprKind::Range(lhs.traverse(walk), rhs.traverse(walk), l),
        ExprKind::Path(qself, p) => ExprKind::Path(qself, p),
        ExprKind::AddrOf(borrow, m, expr) => ExprKind::AddrOf(borrow, m, expr.traverse(walk)),
        ExprKind::Break(lbl, arg) => ExprKind::Break(lbl, arg.traverse(walk)),
        ExprKind::Continue(lbl) => ExprKind::Continue(lbl),
        ExprKind::Ret(expr) => ExprKind::Ret(expr.traverse(walk)),
        ExprKind::LlvmInlineAsm(asm) => ExprKind::LlvmInlineAsm(asm),
        ExprKind::InlineAsm(asm) => ExprKind::InlineAsm(asm),
        ExprKind::MacCall(mac) => ExprKind::MacCall(mac),
        ExprKind::Struct(p) => {
            ExprKind::Struct(p.map(|StructExpr { path, fields, rest }| {
                StructExpr {
                    path,
                    fields: fields.traverse(walk),
                    rest: rest.traverse(walk),
                }
            }))
        },
        ExprKind::Repeat(expr, c) => ExprKind::Repeat(expr.traverse(walk), c),
        ExprKind::Paren(arg) => ExprKind::Paren(arg.traverse(walk)),
        ExprKind::Try(arg) => ExprKind::Try(arg.traverse(walk)),
        ExprKind::Yield(arg) => ExprKind::Yield(arg.traverse(walk)),
        ExprKind::Lit(l) => ExprKind::Lit(l),
        ExprKind::Underscore => ExprKind::Underscore,
        ExprKind::Async(cap, nod, block) => ExprKind::Async(cap, nod, block.traverse(walk)),
        ExprKind::TryBlock(blk) => ExprKind::TryBlock(blk.traverse(walk)),
        ExprKind::ConstBlock(blk) => ExprKind::ConstBlock(blk), // TODO
        ExprKind::Err => unimplemented!(),
        ExprKind::Await(_) => unimplemented!(),
    };
    e
}

/*
pub fn traverse_trait_item_def<W: Traversal>(walk: &mut W, mut ti: TraitItem) -> TraitItem {
    ti.kind = match ti.kind {
        TraitItemKind::Const(ty, arg) => TraitItemKind::Const(ty, arg.traverse(walk)),
        TraitItemKind::Method(sig, block) => TraitItemKind::Method(sig, block.traverse(walk)),
        TraitItemKind::Type(bds, t) => TraitItemKind::Type(bds, t),
        TraitItemKind::Macro(mac) => TraitItemKind::Macro(mac),
    };
    ti
}

pub fn traverse_impl_item_def<W: Traversal>(walk: &mut W, mut ii: ImplItem) -> ImplItem {
    ii.kind = match ii.kind {
        ImplItemKind::Const(ty, expr) => ImplItemKind::Const(ty, expr.traverse(walk)),
        ImplItemKind::Method(sig, block) => ImplItemKind::Method(sig, block.traverse(walk)),
        ImplItemKind::TyAlias(t) => ImplItemKind::TyAlias(t),
        ImplItemKind::Macro(mac) => ImplItemKind::Macro(mac),
    };
    ii
}*/

pub fn traverse_assoc_item_def<W: Traversal>(walk: &mut W, mut ai: AssocItem) -> AssocItem {
    ai.kind = match ai.kind {
        AssocItemKind::Const(def, ty, expr) => AssocItemKind::Const(def, ty, expr.traverse(walk)),
        AssocItemKind::Fn(kind) => {
            let FnKind(def, sig, generics, block) = *kind;
            AssocItemKind::Fn(Box::new(FnKind(def, sig, generics, block.traverse(walk))))
        }
        AssocItemKind::TyAlias(t) => AssocItemKind::TyAlias(t),
        AssocItemKind::MacCall(mac) => AssocItemKind::MacCall(mac),
    };
    ai
}

pub fn traverse_block_def<W: Traversal>(walk: &mut W, mut b: Block) -> Block {
    b.stmts = b.stmts.traverse(walk);
    b
}

pub fn traverse_local_def<W: Traversal>(walk: &mut W, mut l: Local) -> Local {
    l.init = l.init.traverse(walk);
    l
}

pub fn traverse_arm_def<W: Traversal>(walk: &mut W, mut a: Arm) -> Arm {
    a.guard = a.guard.traverse(walk);
    a.body = a.body.traverse(walk);
    a
}

pub fn traverse_field_def<W: Traversal>(walk: &mut W, mut f: ExprField) -> ExprField {
    f.expr = f.expr.traverse(walk);
    f
}

pub fn traverse_mod_def<W: Traversal>(walk: &mut W, m: ModKind) -> ModKind {
    match m {
        ModKind::Loaded(items, i, s) => ModKind::Loaded(items.traverse(walk), i, s),
        ModKind::Unloaded => ModKind::Unloaded
    }
}

pub fn traverse_foreign_mod_def<W: Traversal>(walk: &mut W, mut m: ForeignMod) -> ForeignMod {
    m.items = m.items.traverse(walk);
    m
}

pub fn traverse_item_def<W: Traversal>(walk: &mut W, mut i: Item) -> Item {
    i.kind = match i.kind {
        ItemKind::Static(ty, mu, p_expr) => ItemKind::Static(ty, mu, p_expr.traverse(walk)),
        ItemKind::Const(def, ty, p_expr) => ItemKind::Const(def, ty, p_expr.traverse(walk)),
        ItemKind::Fn(f) => {
            let FnKind(def, f, g, blk) = *f;
            ItemKind::Fn(Box::new(FnKind(def, f, g, blk.traverse(walk))))
        }
        ItemKind::Mod(u, m) => ItemKind::Mod(u, m.traverse(walk)),
        ItemKind::ForeignMod(fm) => ItemKind::ForeignMod(fm.traverse(walk)),
        ItemKind::Trait(t) => {
            let TraitKind(a, u, gen, bds, tis) = *t;
            ItemKind::Trait(Box::new(TraitKind(a, u, gen, bds, tis.traverse(walk))))
        }
        ItemKind::Impl(imp) => {
            let ImplKind {
                unsafety,
                polarity,
                defaultness,
                constness,
                generics,
                of_trait,
                self_ty,
                items
            } = *imp;
            ItemKind::Impl(Box::new(ImplKind {
                unsafety,
                polarity,
                defaultness,
                constness,
                generics,
                of_trait,
                self_ty,
                items: items.traverse(walk),
            }))
        }
        ItemKind::Use(u) => ItemKind::Use(u),
        ItemKind::ExternCrate(u) => ItemKind::ExternCrate(u),
        ItemKind::GlobalAsm(u) => ItemKind::GlobalAsm(u),
        ItemKind::TyAlias(a) => ItemKind::TyAlias(a),
        ItemKind::Enum(l, r) => ItemKind::Enum(l, r),
        ItemKind::Struct(l, r) => ItemKind::Struct(l, r),
        ItemKind::Union(l, r) => ItemKind::Union(l, r),
        ItemKind::TraitAlias(l, r) => ItemKind::TraitAlias(l, r),
        ItemKind::MacCall(m) => ItemKind::MacCall(m),
        ItemKind::MacroDef(m) => ItemKind::MacroDef(m),
    };
    i
}

pub fn traverse_struct_rest_def<W: Traversal>(walk: &mut W, i: StructRest) -> StructRest {
    match i {
        StructRest::Base(expr) => StructRest::Base(expr.traverse(walk)),
        StructRest::Rest(sp) => StructRest::Rest(sp),
        StructRest::None => StructRest::None,
    }
}

//! The type checker: import, `infer`, `whnf`, `is_def_eq`, declaration checking.
//! API and mapping rules: docs/CHECKER.md. Behaviour follows the official kernel
//! (`type_checker.cpp`, `inductive.h`, `quot.h`), with canonical typed locals (DESIGN P2).

use crate::bignat::BigNat;
use crate::env::{ConstInfo, ConstKind, CtorInfo, Decl, Env, Hints, InductInfo, NameId, RawExpr, RawLevel, RawLevelNode, RawTag, RecInfo, Safety};
use crate::store::{Level, LevelId, LevelsId, Store, Term, TermId};
use crate::util::{DenseMap, FxHashMap, FxHashSet};

#[derive(Debug)]
pub enum Fail {
    /// The file is invalid.
    Reject(String),
    /// Resource limit or internal failure.
    Fault(String),
}
pub type R<T> = Result<T, Fail>;

pub fn reject<T>(msg: impl Into<String>) -> R<T> {
    Err(Fail::Reject(msg.into()))
}

pub fn fault<T>(msg: impl Into<String>) -> R<T> {
    Err(Fail::Fault(msg.into()))
}

/// Recursion depth limit (M8).
const MAX_DEPTH: u32 = 200_000;
/// Largest numeral the kernel computes: 2^27 bits = 16 MiB.
const MAX_NAT_BITS: u64 = 1 << 27;
/// Largest exponent / shift amount accepted by `Nat.pow` / `Nat.shiftLeft` reduction.
const MAX_COUNT: u64 = 1 << 24;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Status {
    Continue,
    DefUnknown,
    DefEqual,
    DefDiff,
}

#[inline]
fn ordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

/// Reducibility-hint comparison of the reference kernel: `< 0` unfolds the first argument.
fn compare_hints(h1: Hints, h2: Hints) -> i32 {
    match (h1, h2) {
        (Hints::Regular(a), Hints::Regular(b)) => {
            if a == b {
                0
            } else if a > b {
                -1
            } else {
                1
            }
        }
        (Hints::Opaque, Hints::Opaque) | (Hints::Abbrev, Hints::Abbrev) => 0,
        (Hints::Opaque, _) => 1,
        (_, Hints::Opaque) => -1,
        (Hints::Abbrev, _) => -1,
        (_, Hints::Abbrev) => 1,

    }
}

pub struct Checker<'e> {
    pub store: Store,
    pub env: &'e Env,
    /// Position of the declaration being checked.
    pub pos: u32,
    /// Set by inductive.rs: constants (types and constructors) of the block at `pos` are visible.
    pub allow_block: bool,
    /// True while checking a safe declaration (always, since unsafe ones are not checked).
    pub safe_mode: bool,
    /// Set while checking the argument of an `eagerReduce` application.
    pub eager_reduce: bool,
    /// Operation counters for tracing: infer, whnf_core, whnf, is_def_eq_core, inductive_reduce_rec, rec-rule substitutions.
    pub stats: [u64; 6],
    depth: u32,
    imp_expr: Vec<TermId>,
    imp_level: Vec<LevelId>,
    /// Reusable argument buffers (see `take_buf` / `give_buf`).
    buf_pool: Vec<Vec<TermId>>,
    infer_chk: DenseMap,
    infer_only: DenseMap,
    whnf_core_c: DenseMap,
    whnf_c: DenseMap,
    const_ty: FxHashMap<(NameId, LevelsId), TermId>,
    unfold_c: FxHashMap<(NameId, LevelsId), TermId>,
    rule_c: FxHashMap<(NameId, LevelsId, u32), TermId>,
    nat_ok: FxHashMap<NameId, bool>,
    success: FxHashSet<(TermId, TermId)>,
    failure: FxHashSet<(TermId, TermId)>,
    /// Inference context of `infer_ctx`: closed entries, their interned prefix ids
    /// (`ctx_intern`, id 0 = empty), and the running max of their `local_ub`.
    ctx: Vec<TermId>,
    ctx_id: Vec<u32>,
    ctx_ub: Vec<u32>,
    ctx_intern: FxHashMap<(u32, TermId), u32>,
    /// `infer_ctx` results for open terms, keyed by `(term << 32) | CtxId`.
    infer_open_chk: FxHashMap<u64, TermId>,
    infer_open_only: FxHashMap<u64, TermId>,
    /// Closed instances of open terms, keyed by `(term, binder offset, CtxId)`.
    inst_memo: FxHashMap<(TermId, u32, u32), TermId>,
    /// Caches of the substitution-based oracle `infer_subst`.
    sub_chk: DenseMap,
    sub_only: DenseMap,
    /// `PALLADIUM_CHECK_INFER=1`: every top-level `infer` also runs `infer_subst` and compares.
    check_infer: bool,
    in_oracle: bool,
}

impl<'e> Checker<'e> {
    pub fn new(env: &'e Env) -> Self {
        let mut c = Checker {
            store: Store::new(),
            env,
            pos: 0,
            allow_block: false,
            safe_mode: true,
            eager_reduce: false,
            stats: [0; 6],
            depth: 0,
            imp_expr: Vec::new(),
            imp_level: Vec::new(),
            buf_pool: Vec::new(),
            infer_chk: DenseMap::default(),
            infer_only: DenseMap::default(),
            whnf_core_c: DenseMap::default(),
            whnf_c: DenseMap::default(),
            const_ty: FxHashMap::default(),
            unfold_c: FxHashMap::default(),
            rule_c: FxHashMap::default(),
            nat_ok: FxHashMap::default(),
            success: FxHashSet::default(),
            failure: FxHashSet::default(),
            ctx: Vec::new(),
            ctx_id: Vec::new(),
            ctx_ub: Vec::new(),
            ctx_intern: FxHashMap::default(),
            infer_open_chk: FxHashMap::default(),
            infer_open_only: FxHashMap::default(),
            inst_memo: FxHashMap::default(),
            sub_chk: DenseMap::default(),
            sub_only: DenseMap::default(),
            check_infer: std::env::var("PALLADIUM_CHECK_INFER").map_or(false, |v| v == "1"),
            in_oracle: false,
        };
        c.reset();
        c
    }

    /// An empty argument buffer, reusing a previously returned allocation.
    #[inline]
    fn take_buf(&mut self) -> Vec<TermId> {
        self.buf_pool.pop().unwrap_or_default()
    }

    /// Returns an argument buffer to the pool.
    #[inline]
    fn give_buf(&mut self, mut v: Vec<TermId>) {
        if self.buf_pool.len() < 32 {
            v.clear();
            self.buf_pool.push(v);
        }
    }

    /// Clears the store, the import tables and all caches.
    pub fn reset(&mut self) {
        self.store.clear();
        self.imp_expr.clear();
        self.imp_expr.resize(self.env.raw.exprs.len(), 0);
        self.imp_level.clear();
        self.imp_level.resize(self.env.raw.levels.len(), 0);
        self.infer_chk.clear();
        self.infer_only.clear();
        self.const_ty.clear();
        self.unfold_c.clear();
        self.rule_c.clear();
        self.nat_ok.clear();
        self.ctx.clear();
        self.ctx_id.clear();
        self.ctx_ub.clear();
        self.ctx_intern.clear();
        self.infer_open_chk.clear();
        self.infer_open_only.clear();
        self.inst_memo.clear();
        self.sub_chk.clear();
        self.sub_only.clear();
        self.clear_def_caches();
    }

    /// Clears the caches that may hold results computed under a different visibility
    /// (inductive blocks) or under the failure set.
    pub fn clear_def_caches(&mut self) {
        self.whnf_core_c.clear();
        self.whnf_c.clear();
        self.success.clear();
        self.failure.clear();
    }

    /// Human-readable rendering of a term, depth-limited (for diagnostics).
    pub fn show(&self, t: TermId) -> String {
        self.show_depth(t, 12)
    }

    fn show_depth(&self, t: TermId, d: u32) -> String {
        if d == 0 {
            return "...".into();
        }
        match self.store.get(t) {
            Term::BVar(i) => format!("#{i}"),
            Term::Local(l) => format!("x{}", self.store.local_depth(l)),
            Term::Sort(_) => "Sort".into(),
            Term::Const(n, _) => self.env.raw.name_to_string(n),
            Term::App(f, a) => format!("({} {})", self.show_depth(f, d - 1), self.show_depth(a, d - 1)),
            Term::Lam(a, b) => format!("(fun {} => {})", self.show_depth(a, d - 1), self.show_depth(b, d - 1)),
            Term::Pi(a, b) => format!("(({}) -> {})", self.show_depth(a, d - 1), self.show_depth(b, d - 1)),
            Term::Let(a, v, b) => format!(
                "(let {} := {}; {})",
                self.show_depth(a, d - 1),
                self.show_depth(v, d - 1),
                self.show_depth(b, d - 1)
            ),
            Term::Proj(n, i, e) => format!("{}.{}[{}]", self.show_depth(e, d - 1), i, self.env.raw.name_to_string(n)),
            Term::Nat(id) => self.store.nat_value(id).to_decimal(),
            Term::Str(i) => format!("{:?}", self.env.raw.strs[i as usize]),
        }
    }

    // ----- import ----------------------------------------------------------------

    /// Imports a file level (memoised).
    pub fn import_level(&mut self, l: RawLevel) -> LevelId {
        let c = self.imp_level[l as usize];
        if c != 0 {
            return c;
        }
        let env = self.env;
        let r = match env.raw.levels[l as usize] {
            RawLevelNode::Zero => self.store.mk_zero(),
            RawLevelNode::Succ(a) => {
                let x = self.import_level(a);
                self.store.mk_succ(x)
            }
            RawLevelNode::Max(a, b) => {
                let x = self.import_level(a);
                let y = self.import_level(b);
                self.store.mk_max(x, y)
            }
            RawLevelNode::IMax(a, b) => {
                let x = self.import_level(a);
                let y = self.import_level(b);
                self.store.mk_imax(x, y)
            }
            RawLevelNode::Param(n) => self.store.mk_param(n),
        };
        self.imp_level[l as usize] = r;
        r
    }

    /// Imports a file expression (memoised on every node).
    pub fn import_expr(&mut self, e: RawExpr) -> TermId {
        let c = self.imp_expr[e as usize];
        if c != 0 {
            return c;
        }
        let env = self.env;
        let n = env.raw.exprs[e as usize];
        let r = match n.tag {
            RawTag::BVar => self.store.mk_bvar(n.a),
            RawTag::Sort => {
                let l = self.import_level(n.a);
                self.store.mk_sort(l)
            }
            RawTag::Const => {
                let mut ls = Vec::with_capacity(n.c as usize);
                for i in 0..n.c as usize {
                    let rl = env.raw.const_levels[n.b as usize + i];
                    ls.push(self.import_level(rl));
                }
                let lv = self.store.mk_levels(&ls);
                self.store.mk_const(n.a, lv)
            }
            RawTag::App => {
                let f = self.import_expr(n.a);
                let a = self.import_expr(n.b);
                self.store.mk_app(f, a)
            }
            RawTag::Lam => {
                let d = self.import_expr(n.a);
                let b = self.import_expr(n.b);
                self.store.mk_lam(d, b)
            }
            RawTag::Pi => {
                let d = self.import_expr(n.a);
                let b = self.import_expr(n.b);
                self.store.mk_pi(d, b)
            }
            RawTag::Let => {
                let t = self.import_expr(n.a);
                let v = self.import_expr(n.b);
                let b = self.import_expr(n.c);
                self.store.mk_let(t, v, b)
            }
            RawTag::Proj => {
                let x = self.import_expr(n.c);
                self.store.mk_proj(n.a, n.b, x)
            }
            RawTag::Nat => self.store.mk_nat(&env.raw.nats[n.a as usize]),
            RawTag::Str => self.store.mk_str(n.a),
        };
        self.imp_expr[e as usize] = r;
        r
    }

    // ----- constants -------------------------------------------------------------

    /// Visibility (P6): constants of earlier positions; block types and constructors at `pos`
    /// when `allow_block` is set. Recursors of the block are never visible.
    pub fn const_info_opt(&self, n: NameId) -> Option<&'e ConstInfo> {
        let env = self.env;
        let info = env.get(n)?;
        if info.pos < self.pos {
            return Some(info);
        }
        if info.pos == self.pos && self.allow_block && matches!(info.kind, ConstKind::Induct(_) | ConstKind::Ctor(_)) {
            return Some(info);
        }
        None
    }

    pub fn const_info(&self, n: NameId) -> R<&'e ConstInfo> {
        match self.const_info_opt(n) {
            Some(i) => Ok(i),
            None => reject(format!("unknown constant '{}'", self.env.raw.name_to_string(n))),
        }
    }

    fn subst_levels(&mut self, t: TermId, params: &[NameId], ls: LevelsId) -> TermId {
        if params.is_empty() {
            t
        } else {
            self.store.subst_params(t, params, ls)
        }
    }

    /// The type of constant `n` instantiated with levels `ls` (cached).
    pub fn const_type(&mut self, n: NameId, ls: LevelsId) -> R<TermId> {
        if let Some(&t) = self.const_ty.get(&(n, ls)) {
            return Ok(t);
        }
        let info = self.const_info(n)?;
        if self.store.levels(ls).len() != info.level_params.len() {
            return reject(format!("incorrect number of universe levels for '{}'", self.env.raw.name_to_string(n)));
        }
        let ty = self.import_expr(info.ty);
        let t = self.subst_levels(ty, &info.level_params, ls);
        self.const_ty.insert((n, ls), t);
        Ok(t)
    }

    /// Head constant of `e` if it is a visible definition or theorem with matching arity.
    fn is_delta(&self, e: TermId) -> Option<(NameId, Hints)> {
        let f = self.store.app_fn(e);
        if let Term::Const(n, ls) = self.store.get(f) {
            let info = self.const_info_opt(n)?;
            let hints = match &info.kind {
                ConstKind::Def { hints, .. } => *hints,
                ConstKind::Thm { .. } => Hints::Opaque,
                _ => return None,
            };
            if self.store.levels(ls).len() == info.level_params.len() {
                return Some((n, hints));
            }
        }
        None
    }

    fn unfold_definition_core(&mut self, e: TermId) -> R<Option<TermId>> {
        let Term::Const(n, ls) = self.store.get(e) else { return Ok(None) };
        let Some(info) = self.const_info_opt(n) else { return Ok(None) };
        let value = match &info.kind {
            ConstKind::Def { value, .. } | ConstKind::Thm { value, .. } => *value,
            _ => return Ok(None),
        };
        if self.store.levels(ls).len() != info.level_params.len() {
            return Ok(None);
        }
        if let Some(&t) = self.unfold_c.get(&(n, ls)) {
            return Ok(Some(t));
        }
        let v = self.import_expr(value);
        let t = self.subst_levels(v, &info.level_params, ls);
        self.unfold_c.insert((n, ls), t);
        Ok(Some(t))
    }

    fn unfold_definition(&mut self, e: TermId) -> R<Option<TermId>> {
        if let Term::App(..) = self.store.get(e) {
            let mut args = Vec::new();
            let f0 = self.store.unfold_app(e, &mut args);
            match self.unfold_definition_core(f0)? {
                Some(f) => Ok(Some(self.store.mk_app_n(f, &args))),
                None => Ok(None),
            }
        } else {
            self.unfold_definition_core(e)
        }
    }

    // ----- locals and telescopes -------------------------------------------------

    /// A local of type `ty` at depth `max(*next, local_ub(ty))`; advances `*next` (M1).
    pub(crate) fn fresh_local(&mut self, next: &mut u32, ty: TermId) -> TermId {
        let d = (*next).max(self.store.local_ub(ty));
        *next = d + 1;
        self.store.mk_local(d, ty)
    }

    /// Opens the leading binders of `t` (a Lam if `want_lam`, else a Pi). Returns the locals,
    /// the original (loose-bvar) domains, and the instantiated body.
    fn open_telescope(&mut self, t: TermId, want_lam: bool) -> (Vec<TermId>, Vec<TermId>, TermId) {
        let mut xs: Vec<TermId> = Vec::new();
        let mut doms: Vec<TermId> = Vec::new();
        let mut cur = t;
        let mut next = self.store.local_ub(t);
        loop {
            let (d, b) = match self.store.get(cur) {
                Term::Lam(d, b) if want_lam => (d, b),
                Term::Pi(d, b) if !want_lam => (d, b),
                _ => break,
            };
            let dinst = self.store.instantiate(d, &xs);
            let x = self.fresh_local(&mut next, dinst);
            xs.push(x);
            doms.push(d);
            cur = b;
        }
        let body = self.store.instantiate(cur, &xs);
        (xs, doms, body)
    }

    /// Opens one binder of a Lam/Pi `binder` (M1). `extra_ub` raises the local's depth so that
    /// it also avoids a second term. Returns the local and the instantiated body. A non-binder
    /// is returned unchanged (the caller only passes binders).
    pub fn open_binder(&mut self, binder: TermId, extra_ub: u32) -> (TermId, TermId) {
        let (d, b) = match self.store.get(binder) {
            Term::Lam(d, b) | Term::Pi(d, b) => (d, b),
            _ => return (binder, binder),
        };
        let mut next = self.store.local_ub(binder).max(extra_ub);
        let x = self.fresh_local(&mut next, d);
        let body = self.store.instantiate(b, &[x]);
        (x, body)
    }

    // ----- typing ----------------------------------------------------------------
    //
    // `infer_ctx` is the implementation (docs/EVAL.md Part B). The context is a stack of
    // closed terms `ctx`: a `Local` for each enclosing Lam/Pi binder, the instantiated value
    // for each enclosing let. A loose bvar `i` of the term being inferred refers to
    // `ctx[len-1-i]`, so no binder body is ever substituted. `infer_subst*` is the old
    // substitution-based code, kept as the oracle for `PALLADIUM_CHECK_INFER=1`.

    pub fn check(&mut self, t: TermId) -> R<TermId> {
        self.infer(t, true)
    }

    /// The type of the closed term `t`. `check == false` assumes `t` is well typed.
    pub fn infer(&mut self, t: TermId, check: bool) -> R<TermId> {
        if self.store.lbr(t) > 0 {
            return reject("type checker does not support loose bound variables");
        }
        if !self.check_infer || self.in_oracle {
            return self.infer_top(t, check);
        }
        // Oracle: the new result must equal (or be def-eq to) the substitution-based one.
        let new = self.infer_top(t, check);
        self.in_oracle = true;
        let old = self.infer_subst(t, check);
        let agree = match (&new, &old) {
            (Ok(n), Ok(o)) => *n == *o || matches!(self.is_def_eq(*n, *o), Ok(true)),
            (Err(_), Err(_)) => true,
            _ => false,
        };
        if !agree {
            let show_new = match &new {
                Ok(n) => self.show(*n),
                Err(e) => format!("{e:?}"),
            };
            let show_old = match &old {
                Ok(o) => self.show(*o),
                Err(e) => format!("{e:?}"),
            };
            self.in_oracle = false;
            panic!(
                "PALLADIUM_CHECK_INFER: infer disagrees on {}\n  new: {}\n  old: {}",
                self.show(t),
                show_new,
                show_old
            );
        }
        self.in_oracle = false;
        new
    }

    /// `infer_ctx` with an empty context (the context of a closed term).
    fn infer_top(&mut self, t: TermId, check: bool) -> R<TermId> {
        if self.ctx.is_empty() {
            return self.infer_ctx(t, check);
        }
        let ctx = std::mem::take(&mut self.ctx);
        let ids = std::mem::take(&mut self.ctx_id);
        let ubs = std::mem::take(&mut self.ctx_ub);
        let r = self.infer_ctx(t, check);
        self.ctx = ctx;
        self.ctx_id = ids;
        self.ctx_ub = ubs;
        r
    }

    // ----- context ---------------------------------------------------------------

    #[inline]
    fn ctx_cur_id(&self) -> u32 {
        self.ctx_id.last().copied().unwrap_or(0)
    }

    #[inline]
    fn ctx_cur_ub(&self) -> u32 {
        self.ctx_ub.last().copied().unwrap_or(0)
    }

    /// Pushes a closed entry; `ctx_id` interns the prefix, `ctx_ub` is the running max of `local_ub`.
    fn ctx_push(&mut self, e: TermId) {
        let parent = self.ctx_cur_id();
        let next = self.ctx_intern.len() as u32 + 1;
        let id = *self.ctx_intern.entry((parent, e)).or_insert(next);
        let ub = self.ctx_cur_ub().max(self.store.local_ub(e));
        self.ctx.push(e);
        self.ctx_id.push(id);
        self.ctx_ub.push(ub);
    }

    fn ctx_pop(&mut self) {
        self.ctx.pop();
        self.ctx_id.pop();
        self.ctx_ub.pop();
    }

    /// A fresh local for the binder of `t` with closed domain `dom`. Its depth is at least the
    /// context's `ctx_ub` and the `local_ub` of `t` and `dom`, so it occurs in nothing else (P2).
    fn fresh_ctx_local(&mut self, t: TermId, dom: TermId) -> TermId {
        let d = self.ctx_cur_ub().max(self.store.local_ub(t)).max(self.store.local_ub(dom));
        self.store.mk_local(d, dom)
    }

    /// The closed instance of `t` under the current context (`t` itself when closed).
    /// Memoised on (subterm, binder offset, CtxId) across calls.
    fn inst_ctx(&mut self, t: TermId) -> R<TermId> {
        if self.store.lbr(t) == 0 {
            return Ok(t);
        }
        self.inst_rec(t, 0)
    }

    fn inst_rec(&mut self, t: TermId, off: u32) -> R<TermId> {
        if self.store.lbr(t) <= off {
            return Ok(t);
        }
        let key = (t, off, self.ctx_cur_id());
        if let Some(&r) = self.inst_memo.get(&key) {
            return Ok(r);
        }
        let r = match self.store.get(t) {
            Term::BVar(i) => {
                // lbr(t) > off, so i >= off.
                let k = (i - off) as usize;
                let len = self.ctx.len();
                if k >= len {
                    return reject("loose bound variable");
                }
                self.ctx[len - 1 - k]
            }
            Term::App(f, a) => {
                let f2 = self.inst_rec(f, off)?;
                let a2 = self.inst_rec(a, off)?;
                self.store.mk_app(f2, a2)
            }
            Term::Lam(d, b) => {
                let d2 = self.inst_rec(d, off)?;
                let b2 = self.inst_rec(b, off + 1)?;
                self.store.mk_lam(d2, b2)
            }
            Term::Pi(d, b) => {
                let d2 = self.inst_rec(d, off)?;
                let b2 = self.inst_rec(b, off + 1)?;
                self.store.mk_pi(d2, b2)
            }
            Term::Let(ty, v, b) => {
                let ty2 = self.inst_rec(ty, off)?;
                let v2 = self.inst_rec(v, off)?;
                let b2 = self.inst_rec(b, off + 1)?;
                self.store.mk_let(ty2, v2, b2)
            }
            Term::Proj(s, i, e) => {
                let e2 = self.inst_rec(e, off)?;
                self.store.mk_proj(s, i, e2)
            }
            _ => t,
        };
        self.inst_memo.insert(key, r);
        Ok(r)
    }

    /// Checks `inst(ft)` for the pending arguments `args` (binder order, outermost first).
    /// Instances are built only when `ft` has loose bvars.
    fn inst_pending(&mut self, ft: TermId, args: &[TermId]) -> R<TermId> {
        if args.is_empty() || self.store.lbr(ft) == 0 {
            return Ok(ft);
        }
        let mut xs = Vec::with_capacity(args.len());
        for &a in args {
            xs.push(self.inst_ctx(a)?);
        }
        Ok(self.store.instantiate(ft, &xs))
    }

    // ----- infer_ctx -------------------------------------------------------------

    fn infer_ctx(&mut self, t: TermId, check: bool) -> R<TermId> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return fault("recursion depth exceeded");
        }
        let r = self.infer_ctx_core(t, check);
        self.depth -= 1;
        r
    }

    fn infer_ctx_core(&mut self, t: TermId, check: bool) -> R<TermId> {
        self.stats[0] += 1;
        let closed = self.store.lbr(t) == 0;
        let key = ((t as u64) << 32) | self.ctx_cur_id() as u64;
        if closed {
            if let Some(r) = self.infer_chk.get(t) {
                return Ok(r);
            }
            if !check {
                if let Some(r) = self.infer_only.get(t) {
                    return Ok(r);
                }
            }
        } else {
            if let Some(&r) = self.infer_open_chk.get(&key) {
                return Ok(r);
            }
            if !check {
                if let Some(&r) = self.infer_open_only.get(&key) {
                    return Ok(r);
                }
            }
        }
        let r = self.infer_node(t, check)?;
        match (closed, check) {
            (true, true) => self.infer_chk.insert(t, r),
            (true, false) => self.infer_only.insert(t, r),
            (false, true) => {
                self.infer_open_chk.insert(key, r);
            }
            (false, false) => {
                self.infer_open_only.insert(key, r);
            }
        }
        Ok(r)
    }

    fn infer_node(&mut self, t: TermId, check: bool) -> R<TermId> {
        match self.store.get(t) {
            Term::BVar(i) => {
                let len = self.ctx.len();
                if i as usize >= len {
                    return reject("loose bound variable");
                }
                let e = self.ctx[len - 1 - i as usize];
                self.infer_ctx(e, check)
            }
            Term::Local(l) => Ok(self.store.local_type(l)),
            Term::Sort(l) => {
                let s = self.store.mk_succ(l);
                Ok(self.store.mk_sort(s))
            }
            Term::Const(n, ls) => self.infer_const(n, ls, check),
            Term::App(..) => self.infer_app_ctx(t, check),
            Term::Lam(..) => self.infer_lambda_ctx(t, check),
            Term::Pi(..) => self.infer_pi_ctx(t, check),
            Term::Let(ty, v, b) => self.infer_let_ctx(ty, v, b, check),
            Term::Proj(s, i, e) => {
                if self.store.lbr(t) == 0 {
                    let ty0 = self.infer_ctx(e, check)?;
                    self.proj_type(s, i, e, ty0)
                } else {
                    let c = self.inst_ctx(t)?;
                    self.infer(c, check)
                }
            }
            Term::Nat(_) | Term::Str(_) => self.infer_lit(t, check),
        }
    }

    fn infer_app_ctx(&mut self, t: TermId, check: bool) -> R<TermId> {
        if check {
            let Term::App(f, a) = self.store.get(t) else { return fault("infer_app") };
            let ft0 = self.infer_ctx(f, true)?;
            let (dom, body) = self.ensure_pi(ft0)?;
            let at = self.infer_ctx(a, true)?;
            if !self.check_arg(a, at, dom)? {
                return reject("application type mismatch");
            }
            if self.store.lbr(body) == 0 {
                return Ok(body);
            }
            let ai = self.inst_ctx(a)?;
            Ok(self.store.instantiate(body, &[ai]))
        } else {
            let mut args = self.take_buf();
            let f = self.store.unfold_app(t, &mut args);
            let r = self.infer_spine_ctx(f, &args);
            self.give_buf(args);
            r
        }
    }

    /// Infer-only spine: the codomain is instantiated lazily, only when it has loose bvars.
    fn infer_spine_ctx(&mut self, f: TermId, args: &[TermId]) -> R<TermId> {
        let mut ft = self.infer_ctx(f, false)?;
        let mut j = 0;
        for i in 0..args.len() {
            if let Term::Pi(_, b) = self.store.get(ft) {
                ft = b;
            } else {
                ft = self.inst_pending(ft, &args[j..i])?;
                let (_, b) = self.ensure_pi(ft)?;
                ft = b;
                j = i;
            }
        }
        self.inst_pending(ft, &args[j..])
    }

    fn infer_lambda_ctx(&mut self, t: TermId, check: bool) -> R<TermId> {
        let Term::Lam(ty, b) = self.store.get(t) else { return fault("infer_lambda") };
        let dom = self.inst_ctx(ty)?;
        if check {
            let s = self.infer_ctx(dom, true)?;
            self.ensure_sort(s)?;
        }
        if self.store.lbr(b) == 0 {
            let r = self.infer_ctx(b, check)?;
            return Ok(self.store.mk_pi(dom, r));
        }
        let x = self.fresh_ctx_local(t, dom);
        self.ctx_push(x);
        let r = self.infer_ctx(b, check);
        self.ctx_pop();
        let r = self.store.abstract_locals(r?, &[x]);
        Ok(self.store.mk_pi(dom, r))
    }

    fn infer_pi_ctx(&mut self, t: TermId, check: bool) -> R<TermId> {
        let Term::Pi(ty, b) = self.store.get(t) else { return fault("infer_pi") };
        let dom = self.inst_ctx(ty)?;
        let s = self.infer_ctx(dom, check)?;
        let u = self.ensure_sort(s)?;
        let s2 = if self.store.lbr(b) == 0 {
            self.infer_ctx(b, check)?
        } else {
            let x = self.fresh_ctx_local(t, dom);
            self.ctx_push(x);
            let r = self.infer_ctx(b, check);
            self.ctx_pop();
            r?
        };
        let v = self.ensure_sort(s2)?;
        let r = self.store.mk_imax(u, v);
        Ok(self.store.mk_sort(r))
    }

    fn infer_let_ctx(&mut self, ty: TermId, v: TermId, b: TermId, check: bool) -> R<TermId> {
        let dom = self.inst_ctx(ty)?;
        let vi = self.inst_ctx(v)?;
        if check {
            let s = self.infer_ctx(dom, true)?;
            self.ensure_sort(s)?;
            let vt = self.infer_ctx(vi, true)?;
            if !self.is_def_eq(vt, dom)? {
                return reject("let value type mismatch");
            }
        }
        if self.store.lbr(b) == 0 {
            return self.infer_ctx(b, check);
        }
        self.ctx_push(vi);
        let r = self.infer_ctx(b, check);
        self.ctx_pop();
        r
    }

    // ----- infer (substitution-based oracle) -------------------------------------

    /// The old implementation: binders are opened by substituting into the body.
    fn infer_subst(&mut self, t: TermId, check: bool) -> R<TermId> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return fault("recursion depth exceeded");
        }
        let r = self.infer_subst_core(t, check);
        self.depth -= 1;
        r
    }

    fn infer_subst_core(&mut self, t: TermId, check: bool) -> R<TermId> {
        if self.store.lbr(t) > 0 {
            return reject("type checker does not support loose bound variables");
        }
        if let Some(r) = self.sub_chk.get(t) {
            return Ok(r);
        }
        if !check {
            if let Some(r) = self.sub_only.get(t) {
                return Ok(r);
            }
        }
        let r = match self.store.get(t) {
            Term::BVar(_) => return reject("loose bound variable"),
            Term::Local(l) => self.store.local_type(l),
            Term::Sort(l) => {
                let s = self.store.mk_succ(l);
                self.store.mk_sort(s)
            }
            Term::Const(n, ls) => self.infer_const(n, ls, check)?,
            Term::App(..) => self.infer_app_subst(t, check)?,
            Term::Lam(..) => self.infer_lambda_subst(t, check)?,
            Term::Pi(..) => self.infer_pi_subst(t, check)?,
            Term::Let(ty, v, b) => self.infer_let_subst(ty, v, b, check)?,
            Term::Proj(s, i, e) => {
                let ty0 = self.infer_subst(e, check)?;
                self.proj_type(s, i, e, ty0)?
            }
            Term::Nat(_) | Term::Str(_) => self.infer_lit(t, check)?,
        };
        if check {
            self.sub_chk.insert(t, r);
        } else {
            self.sub_only.insert(t, r);
        }
        Ok(r)
    }

    fn infer_app_subst(&mut self, t: TermId, check: bool) -> R<TermId> {
        if check {
            let Term::App(f, a) = self.store.get(t) else { return fault("infer_app") };
            let ft0 = self.infer_subst(f, true)?;
            let (dom, body) = self.ensure_pi(ft0)?;
            let at = self.infer_subst(a, true)?;
            if !self.check_arg(a, at, dom)? {
                return reject("application type mismatch");
            }
            Ok(self.store.instantiate(body, &[a]))
        } else {
            let mut args = Vec::new();
            let f = self.store.unfold_app(t, &mut args);
            let mut ft = self.infer_subst(f, false)?;
            let mut j = 0;
            for i in 0..args.len() {
                if let Term::Pi(_, b) = self.store.get(ft) {
                    ft = b;
                } else {
                    ft = self.store.instantiate(ft, &args[j..i]);
                    let (_, b) = self.ensure_pi(ft)?;
                    ft = b;
                    j = i;
                }
            }
            Ok(self.store.instantiate(ft, &args[j..]))
        }
    }

    fn infer_lambda_subst(&mut self, t: TermId, check: bool) -> R<TermId> {
        let (xs, doms, body) = self.open_telescope(t, true);
        if check {
            for &x in &xs {
                let d = match self.store.get(x) {
                    Term::Local(l) => self.store.local_type(l),
                    _ => return fault("open_telescope"),
                };
                let s = self.infer_subst(d, true)?;
                self.ensure_sort(s)?;
            }
        }
        let r = self.infer_subst(body, check)?;
        let mut res = self.store.abstract_locals(r, &xs);
        for i in (0..xs.len()).rev() {
            res = self.store.mk_pi(doms[i], res);
        }
        Ok(res)
    }

    fn infer_pi_subst(&mut self, t: TermId, check: bool) -> R<TermId> {
        let (xs, _doms, body) = self.open_telescope(t, false);
        let mut us = Vec::with_capacity(xs.len());
        for &x in &xs {
            let d = match self.store.get(x) {
                Term::Local(l) => self.store.local_type(l),
                _ => return fault("open_telescope"),
            };
            let s = self.infer_subst(d, check)?;
            us.push(self.ensure_sort(s)?);
        }
        let s = self.infer_subst(body, check)?;
        let mut r = self.ensure_sort(s)?;
        for &u in us.iter().rev() {
            r = self.store.mk_imax(u, r);
        }
        Ok(self.store.mk_sort(r))
    }

    fn infer_let_subst(&mut self, ty: TermId, v: TermId, b: TermId, check: bool) -> R<TermId> {
        if check {
            let s = self.infer_subst(ty, true)?;
            self.ensure_sort(s)?;
            let vt = self.infer_subst(v, true)?;
            if !self.is_def_eq(vt, ty)? {
                return reject("let value type mismatch");
            }
        }
        let body = self.store.instantiate(b, &[v]);
        self.infer_subst(body, check)
    }

    // ----- shared helpers --------------------------------------------------------

    fn is_eager_reduce_arg(&self, a: TermId) -> bool {
        let Some(en) = self.env.builtins.eager_reduce else { return false };
        if self.store.app_num_args(a) != 2 {
            return false;
        }
        matches!(self.store.get(self.store.app_fn(a)), Term::Const(n, _) if n == en)
    }

    /// Argument `a` of type `at` against the domain `dom` (both closed); `eagerReduce` arguments
    /// are compared with the `Bool.true` shortcut enabled.
    fn check_arg(&mut self, a: TermId, at: TermId, dom: TermId) -> R<bool> {
        if self.is_eager_reduce_arg(a) {
            let old = self.eager_reduce;
            self.eager_reduce = true;
            let r = self.is_def_eq(at, dom);
            self.eager_reduce = old;
            r
        } else {
            self.is_def_eq(at, dom)
        }
    }

    fn infer_const(&mut self, n: NameId, ls: LevelsId, check: bool) -> R<TermId> {
        let info = self.const_info(n)?;
        if check && info.is_unsafe && self.safe_mode {
            return reject(format!("safe declaration uses unsafe constant '{}'", self.env.raw.name_to_string(n)));
        }
        self.const_type(n, ls)
    }

    fn infer_lit(&mut self, t: TermId, check: bool) -> R<TermId> {
        let (name, msg) = match self.store.get(t) {
            Term::Nat(_) => (self.env.builtins.nat_ty, "Nat literal but Nat is not declared"),
            _ => (self.env.builtins.string_ty, "string literal but String is not declared"),
        };
        let Some(n) = name else { return reject(msg) };
        if check {
            self.const_info(n)?;
        }
        let lv = self.store.mk_levels(&[]);
        Ok(self.store.mk_const(n, lv))
    }

    /// The type of `Proj(sname, idx, e)` given the closed type `ty0` of `e` (M9).
    fn proj_type(&mut self, sname: NameId, idx: u32, e: TermId, ty0: TermId) -> R<TermId> {
        let ty = self.whnf(ty0)?;
        let mut args = Vec::new();
        let head = self.store.unfold_app(ty, &mut args);
        let Term::Const(iname, ils) = self.store.get(head) else { return reject("invalid projection") };
        if iname != sname {
            return reject("invalid projection: structure name mismatch");
        }
        let Some(info) = self.const_info_opt(iname) else { return reject("invalid projection") };
        let ConstKind::Induct(iv) = &info.kind else { return reject("invalid projection: not an inductive") };
        if iv.ctors.len() != 1 || args.len() != (iv.num_params + iv.num_indices) as usize {
            return reject("invalid projection: wrong shape");
        }
        let ctor = iv.ctors[0];
        let nparams = iv.num_params as usize;
        let mut r = self.const_type(ctor, ils)?;
        for i in 0..nparams {
            r = self.whnf(r)?;
            match self.store.get(r) {
                Term::Pi(_, b) => r = self.store.instantiate(b, &[args[i]]),
                _ => return reject("invalid projection: constructor arity"),
            }
        }
        let is_prop_type = self.is_prop(ty)?;
        for i in 0..idx {
            r = self.whnf(r)?;
            let Term::Pi(d, b) = self.store.get(r) else { return reject("invalid projection: field index") };
            if self.store.lbr(b) > 0 {
                if is_prop_type && !self.is_prop(d)? {
                    return reject("invalid projection of a proposition");
                }
                let p = self.store.mk_proj(iname, i, e);
                r = self.store.instantiate(b, &[p]);
            } else {
                r = b;
            }
        }
        r = self.whnf(r)?;
        let Term::Pi(d, _) = self.store.get(r) else { return reject("invalid projection: field index") };
        if is_prop_type && !self.is_prop(d)? {
            return reject("invalid projection of a proposition");
        }
        Ok(d)
    }

    /// `whnf(ty)` must be a sort; returns its level.
    pub fn ensure_sort(&mut self, ty: TermId) -> R<LevelId> {
        if let Term::Sort(l) = self.store.get(ty) {
            return Ok(l);
        }
        let w = self.whnf(ty)?;
        match self.store.get(w) {
            Term::Sort(l) => Ok(l),
            _ => reject("type expected"),
        }
    }

    /// `whnf(ty)` must be a Pi; returns (domain, body).
    pub fn ensure_pi(&mut self, ty: TermId) -> R<(TermId, TermId)> {
        if let Term::Pi(d, b) = self.store.get(ty) {
            return Ok((d, b));
        }
        let w = self.whnf(ty)?;
        match self.store.get(w) {
            Term::Pi(d, b) => Ok((d, b)),
            _ => reject("function expected"),
        }
    }

    /// `ty` is a proposition: its type is `Sort l` with `l` zero.
    pub fn is_prop(&mut self, ty: TermId) -> R<bool> {
        let s = self.infer(ty, false)?;
        let l = self.ensure_sort(s)?;
        Ok(self.store.level_is_zero(l))
    }

    // ----- reduction -------------------------------------------------------------

    /// Weak head normal form without delta (and without extensions).
    pub fn whnf_core(&mut self, t: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return fault("recursion depth exceeded");
        }
        let r = self.whnf_core_inner(t, cheap_rec, cheap_proj);
        self.depth -= 1;
        r
    }

    fn whnf_core_inner(&mut self, t: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId> {
        self.stats[1] += 1;
        match self.store.get(t) {
            Term::BVar(_) | Term::Sort(_) | Term::Pi(..) | Term::Const(..) | Term::Lam(..) | Term::Nat(_) | Term::Str(_) | Term::Local(_) => {
                return Ok(t)
            }
            _ => {}
        }
        let cacheable = !cheap_rec && !cheap_proj;
        if cacheable {
            if let Some(r) = self.whnf_core_c.get(t) {
                return Ok(r);
            }
        }
        let r = match self.store.get(t) {
            Term::Let(_, v, b) => {
                let inst = self.store.instantiate(b, &[v]);
                self.whnf_core(inst, cheap_rec, cheap_proj)?
            }
            Term::Proj(s, i, e) => match self.reduce_proj(s, i, e, cheap_rec, cheap_proj)? {
                Some(m) => self.whnf_core(m, cheap_rec, cheap_proj)?,
                None => t,
            },
            Term::App(..) => {
                let mut args = self.take_buf();
                let f0 = self.store.unfold_app(t, &mut args);
                let f = self.whnf_core(f0, cheap_rec, cheap_proj)?;
                if let Term::Lam(..) = self.store.get(f) {
                    let r = self.store.beta(f, &args);
                    self.give_buf(args);
                    self.whnf_core(r, cheap_rec, cheap_proj)?
                } else if f == f0 {
                    self.give_buf(args);
                    match self.reduce_recursor(t, cheap_rec, cheap_proj)? {
                        Some(r) => self.whnf_core(r, cheap_rec, cheap_proj)?,
                        None => t,
                    }
                } else {
                    let r = self.store.mk_app_n(f, &args);
                    self.give_buf(args);
                    self.whnf_core(r, cheap_rec, cheap_proj)?
                }
            }
            _ => t,
        };
        if cacheable {
            self.whnf_core_c.insert(t, r);
        }
        Ok(r)
    }

    fn reduce_proj(&mut self, sname: NameId, idx: u32, e: TermId, cheap_rec: bool, cheap_proj: bool) -> R<Option<TermId>> {
        let c = if cheap_proj { self.whnf_core(e, cheap_rec, cheap_proj)? } else { self.whnf(e)? };
        self.reduce_proj_core(c, sname, idx)
    }

    fn reduce_proj_core(&mut self, c: TermId, sname: NameId, idx: u32) -> R<Option<TermId>> {
        let mut c = c;
        if let Term::Str(_) = self.store.get(c) {
            let k = self.string_lit_to_constructor(c)?;
            c = self.whnf(k)?;
        }
        let mut args = Vec::new();
        let mk = self.store.unfold_app(c, &mut args);
        let Term::Const(n, _) = self.store.get(mk) else { return Ok(None) };
        let Some(info) = self.const_info_opt(n) else { return Ok(None) };
        let ConstKind::Ctor(ci) = &info.kind else { return Ok(None) };
        if ci.induct != sname {
            return Ok(None);
        }
        let k = ci.num_params as u64 + idx as u64;
        if k < args.len() as u64 {
            Ok(Some(args[k as usize]))
        } else {
            Ok(None)
        }
    }

    fn reduce_recursor(&mut self, e: TermId, cheap_rec: bool, cheap_proj: bool) -> R<Option<TermId>> {
        if self.quot_enabled() {
            if let Some(r) = self.quot_reduce_rec(e)? {
                return Ok(Some(r));
            }
        }
        self.inductive_reduce_rec(e, cheap_rec, cheap_proj)
    }

    /// `whnf` used inside recursor reduction: `whnf_core` when `cheap_rec`.
    fn rec_whnf(&mut self, t: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId> {
        if cheap_rec {
            self.whnf_core(t, cheap_rec, cheap_proj)
        } else {
            self.whnf(t)
        }
    }

    /// Quotients are usable when the four `Quot` constants are visible and of the right kind.
    pub fn quot_enabled(&self) -> bool {
        let b = &self.env.builtins;
        let ok = |n: Option<NameId>| match n {
            Some(n) => matches!(self.const_info_opt(n).map(|i| &i.kind), Some(ConstKind::Quot(_))),
            None => false,
        };
        ok(b.quot_ty) && ok(b.quot_mk) && ok(b.quot_lift) && ok(b.quot_ind)
    }

    /// `quot_reduce_rec` of quot.h.
    fn quot_reduce_rec(&mut self, e: TermId) -> R<Option<TermId>> {
        let fnc = self.store.app_fn(e);
        let Term::Const(n, _) = self.store.get(fnc) else { return Ok(None) };
        let (mk_pos, arg_pos) = if Some(n) == self.env.builtins.quot_lift {
            (5usize, 3usize)
        } else if Some(n) == self.env.builtins.quot_ind {
            (4usize, 3usize)
        } else {
            return Ok(None);
        };
        let mut args = Vec::new();
        self.store.unfold_app(e, &mut args);
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(args[mk_pos])?;
        let mkf = self.store.app_fn(mk);
        let is_mk = matches!(self.store.get(mkf), Term::Const(q, _) if Some(q) == self.env.builtins.quot_mk);
        if !is_mk || self.store.app_num_args(mk) != 3 {
            return Ok(None);
        }
        let Term::App(_, last) = self.store.get(mk) else { return Ok(None) };
        let mut r = self.store.mk_app(args[arg_pos], last);
        let elim_arity = mk_pos + 1;
        if args.len() > elim_arity {
            r = self.store.mk_app_n(r, &args[elim_arity..]);
        }
        Ok(Some(r))
    }

    /// The major premise's inductive type, read from the recursor's file type (as
    /// `recursor_val::get_major_induct`). Walks raw nodes; never indexes out of range.
    fn rec_major_induct(&self, rn: NameId, major_idx: usize) -> Option<NameId> {
        let info = self.env.get(rn)?;
        let raw = &self.env.raw;
        let mut ex = info.ty;
        for _ in 0..major_idx {
            let n = *raw.exprs.get(ex as usize)?;
            if n.tag != RawTag::Pi {
                return None;
            }
            ex = n.b;
        }
        let n = *raw.exprs.get(ex as usize)?;
        if n.tag != RawTag::Pi {
            return None;
        }
        let mut d = n.a;
        loop {
            let dn = *raw.exprs.get(d as usize)?;
            match dn.tag {
                RawTag::App => d = dn.a,
                RawTag::Const => return Some(dn.a),
                _ => return None,
            }
        }
    }

    fn is_non_rec_structure(&self, n: NameId) -> bool {
        match self.const_info_opt(n) {
            Some(i) => match &i.kind {
                ConstKind::Induct(iv) => iv.ctors.len() == 1 && iv.num_indices == 0 && !iv.is_rec,
                _ => false,
            },
            None => false,
        }
    }

    fn is_constructor_app(&self, e: TermId) -> bool {
        let f = self.store.app_fn(e);
        match self.store.get(f) {
            Term::Const(n, _) => match self.const_info_opt(n) {
                Some(i) => matches!(i.kind, ConstKind::Ctor(_)),
                None => false,
            },
            _ => false,
        }
    }

    /// `inductive_reduce_rec` of inductive.h.
    fn inductive_reduce_rec(&mut self, e: TermId, cheap_rec: bool, cheap_proj: bool) -> R<Option<TermId>> {
        let mut rargs = self.take_buf();
        let mut margs = self.take_buf();
        let r = self.inductive_reduce_rec_core(e, cheap_rec, cheap_proj, &mut rargs, &mut margs);
        self.give_buf(rargs);
        self.give_buf(margs);
        r
    }

    fn inductive_reduce_rec_core(
        &mut self,
        e: TermId,
        cheap_rec: bool,
        cheap_proj: bool,
        rargs: &mut Vec<TermId>,
        margs: &mut Vec<TermId>,
    ) -> R<Option<TermId>> {
        self.stats[4] += 1;
        let fnc = self.store.unfold_app(e, rargs);
        let Term::Const(rn, rls) = self.store.get(fnc) else { return Ok(None) };
        let Some(info) = self.const_info_opt(rn) else { return Ok(None) };
        let ConstKind::Rec(rec) = &info.kind else { return Ok(None) };
        let major_idx = rec.num_params as usize + rec.num_motives as usize + rec.num_minors as usize + rec.num_indices as usize;
        if major_idx >= rargs.len() {
            return Ok(None);
        }
        let mut major = rargs[major_idx];
        if rec.k {
            major = self.to_cnstr_when_k(rec, rn, major, cheap_rec, cheap_proj)?;
        }
        let mt = self.infer(major, false)?;
        if !self.is_prop(mt)? {
            major = self.rec_whnf(major, cheap_rec, cheap_proj)?;
        }
        match self.store.get(major) {
            Term::Nat(_) => match self.nat_lit_to_constructor(major) {
                Some(m) => major = m,
                None => return Ok(None),
            },
            Term::Str(_) => {
                let k = self.string_lit_to_constructor(major)?;
                major = self.rec_whnf(k, cheap_rec, cheap_proj)?;
            }
            _ => major = self.to_cnstr_when_structure(rec, rn, major, cheap_rec, cheap_proj)?,
        }
        let mhead = self.store.unfold_app(major, margs);
        let Term::Const(mcn, _) = self.store.get(mhead) else { return Ok(None) };
        let Some((rule_idx, rule)) = rec.rules.iter().enumerate().find(|(_, r)| r.ctor == mcn) else { return Ok(None) };
        let rule_idx = rule_idx as u32;
        if rule.nfields as usize > margs.len() {
            return Ok(None);
        }
        if self.store.levels(rls).len() != info.level_params.len() {
            return Ok(None);
        }
        let rule_key = (rn, rls, rule_idx);
        let rhs0 = match self.rule_c.get(&rule_key) {
            Some(&t) => t,
            None => {
                let raw_rhs = self.import_expr(rule.rhs);
                let t = self.subst_levels(raw_rhs, &info.level_params, rls);
                self.rule_c.insert(rule_key, t);
                t
            }
        };
        let k = rec.num_params as usize + rec.num_motives as usize + rec.num_minors as usize;
        let mut rhs = self.store.mk_app_n(rhs0, &rargs[..k]);
        let nparams_ctor = margs.len() - rule.nfields as usize;
        rhs = self.store.mk_app_n(rhs, &margs[nparams_ctor..]);
        if rargs.len() > major_idx + 1 {
            rhs = self.store.mk_app_n(rhs, &rargs[major_idx + 1..]);
        }
        Ok(Some(rhs))
    }

    /// `to_cnstr_when_K` of inductive.h.
    fn to_cnstr_when_k(&mut self, rec: &RecInfo, rn: NameId, e: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId> {
        let major_idx = rec.num_params as usize + rec.num_motives as usize + rec.num_minors as usize + rec.num_indices as usize;
        let Some(major_induct) = self.rec_major_induct(rn, major_idx) else { return Ok(e) };
        let at0 = self.infer(e, false)?;
        let app_type = self.rec_whnf(at0, cheap_rec, cheap_proj)?;
        let mut targs = Vec::new();
        let head = self.store.unfold_app(app_type, &mut targs);
        let Term::Const(hn, hls) = self.store.get(head) else { return Ok(e) };
        if hn != major_induct {
            return Ok(e);
        }
        let Some(info) = self.const_info_opt(hn) else { return Ok(e) };
        let ConstKind::Induct(iv) = &info.kind else { return Ok(e) };
        let Some(&ctor) = iv.ctors.first() else { return Ok(e) };
        let np = rec.num_params as usize;
        if targs.len() < np {
            return Ok(e);
        }
        let c = self.store.mk_const(ctor, hls);
        let new_app = self.store.mk_app_n(c, &targs[..np]);
        let new_type = self.infer(new_app, false)?;
        if !self.is_def_eq(app_type, new_type)? {
            return Ok(e);
        }
        Ok(new_app)
    }

    /// `to_cnstr_when_structure` of inductive.h.
    fn to_cnstr_when_structure(&mut self, rec: &RecInfo, rn: NameId, e: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId> {
        let major_idx = rec.num_params as usize + rec.num_motives as usize + rec.num_minors as usize + rec.num_indices as usize;
        let Some(induct) = self.rec_major_induct(rn, major_idx) else { return Ok(e) };
        if !self.is_non_rec_structure(induct) || self.is_constructor_app(e) {
            return Ok(e);
        }
        let et0 = self.infer(e, false)?;
        let e_type = self.rec_whnf(et0, cheap_rec, cheap_proj)?;
        let eh = self.store.app_fn(e_type);
        match self.store.get(eh) {
            Term::Const(n, _) if n == induct => {}
            _ => return Ok(e),
        }
        let Some(&all0) = rec.all.first() else { return Ok(e) };
        let Some(all_info) = self.const_info_opt(all0) else { return Ok(e) };
        if self.env.get(rn).map(|i| i.level_params.len()) == Some(all_info.level_params.len()) {
            return Ok(e);
        }
        self.expand_eta_struct(e_type, e)
    }

    fn expand_eta_struct(&mut self, e_type: TermId, e: TermId) -> R<TermId> {
        let mut args = Vec::new();
        let head = self.store.unfold_app(e_type, &mut args);
        let Term::Const(iname, ils) = self.store.get(head) else { return Ok(e) };
        let Some(info) = self.const_info_opt(iname) else { return Ok(e) };
        let ConstKind::Induct(iv) = &info.kind else { return Ok(e) };
        let Some(&ctor) = iv.ctors.first() else { return Ok(e) };
        let Some(cinfo) = self.const_info_opt(ctor) else { return Ok(e) };
        let ConstKind::Ctor(ci) = &cinfo.kind else { return Ok(e) };
        args.truncate(ci.num_params as usize);
        let c = self.store.mk_const(ctor, ils);
        let mut r = self.store.mk_app_n(c, &args);
        for i in 0..ci.num_fields {
            let p = self.store.mk_proj(iname, i, e);
            r = self.store.mk_app(r, p);
        }
        Ok(r)
    }

    /// `nat_lit_to_constructor`: `0` becomes `Nat.zero`, `n+1` becomes `Nat.succ n`.
    fn nat_lit_to_constructor(&mut self, v: TermId) -> Option<TermId> {
        let Term::Nat(id) = self.store.get(v) else { return None };
        let val = self.store.nat_value(id).clone();
        let zero = self.env.builtins.nat_zero?;
        let succ = self.env.builtins.nat_succ?;
        let lv = self.store.mk_levels(&[]);
        if val.is_zero() {
            Some(self.store.mk_const(zero, lv))
        } else {
            let p = val.pred();
            let pt = self.store.mk_nat(&p);
            let s = self.store.mk_const(succ, lv);
            Some(self.store.mk_app(s, pt))
        }
    }

    /// `string_lit_to_constructor`: `String.ofList (List.cons Char (Char.ofNat c) ... List.nil)`.
    pub fn string_lit_to_constructor(&mut self, e: TermId) -> R<TermId> {
        let Term::Str(idx) = self.store.get(e) else { return fault("string_lit_to_constructor") };
        let b = &self.env.builtins;
        let (Some(char_ty), Some(of_nat), Some(cons), Some(nil), Some(of_list)) = (b.char_ty, b.char_of_nat, b.list_cons, b.list_nil, b.string_of_list) else {
            return reject("string literal expansion needs String, Char, List");
        };
        let s = self.env.raw.strs[idx as usize].clone();
        let lv0 = self.store.mk_zero();
        let lv = self.store.mk_levels(&[lv0]);
        let ct = self.store.mk_const(char_ty, 0);
        let nil_c = self.store.mk_const(nil, lv);
        let cons_c = self.store.mk_const(cons, lv);
        let of_nat_c = self.store.mk_const(of_nat, 0);
        let mut acc = self.store.mk_app(nil_c, ct);
        let chars: Vec<char> = s.chars().collect();
        for &c in chars.iter().rev() {
            let n = self.store.mk_nat_u64(c as u64);
            let ch = self.store.mk_app(of_nat_c, n);
            let h = self.store.mk_app(cons_c, ct);
            let h2 = self.store.mk_app(h, ch);
            acc = self.store.mk_app(h2, acc);
        }
        let of_list_c = self.store.mk_const(of_list, 0);
        Ok(self.store.mk_app(of_list_c, acc))
    }

    /// Nat literal value of `e` if it is a literal or `Nat.zero`.
    fn nat_lit_value(&self, e: TermId) -> Option<BigNat> {
        match self.store.get(e) {
            Term::Nat(id) => Some(self.store.nat_value(id).clone()),
            Term::Const(n, ls) if Some(n) == self.env.builtins.nat_zero && self.store.levels(ls).is_empty() => Some(BigNat::zero()),
            _ => None,
        }
    }

    /// True if the builtin `n` is a visible constant without levels whose type is
    /// `Nat^arity -> Nat` (or `-> Bool` when `res_bool`). Cached per name when visible.
    fn nat_builtin_ok(&mut self, n: NameId, arity: u32, res_bool: bool) -> bool {
        if let Some(&b) = self.nat_ok.get(&n) {
            return b;
        }
        let Some(nat) = self.env.builtins.nat_ty else { return false };
        let boolean = if res_bool {
            match self.env.builtins.bool_ty {
                Some(b) => b,
                None => return false,
            }
        } else {
            nat
        };
        let Some(info) = self.const_info_opt(n) else { return false };
        if !info.level_params.is_empty() {
            self.nat_ok.insert(n, false);
            return false;
        }
        let lv = self.store.mk_levels(&[]);
        let natc = self.store.mk_const(nat, lv);
        let res = if res_bool { self.store.mk_const(boolean, lv) } else { natc };
        let mut ty = res;
        for _ in 0..arity {
            ty = self.store.mk_pi(natc, ty);
        }
        let it = self.import_expr(info.ty);
        let ok = it == ty;
        self.nat_ok.insert(n, ok);
        ok
    }

    fn mk_bool_const(&mut self, b: bool) -> Option<TermId> {
        let n = if b { self.env.builtins.bool_true? } else { self.env.builtins.bool_false? };
        let lv = self.store.mk_levels(&[]);
        Some(self.store.mk_const(n, lv))
    }

    /// `reduce_nat`: literal arithmetic on `Nat`, for builtins of the expected shape only.
    fn reduce_nat(&mut self, e: TermId) -> R<Option<TermId>> {
        let Term::App(f, a) = self.store.get(e) else { return Ok(None) };
        if let Term::Const(n, ls) = self.store.get(f) {
            if Some(n) == self.env.builtins.nat_succ && self.store.levels(ls).is_empty() && self.nat_builtin_ok(n, 1, false) {
                let v = self.whnf(a)?;
                let Some(x) = self.nat_lit_value(v) else { return Ok(None) };
                let r = x.succ();
                if r.bit_len() > MAX_NAT_BITS {
                    return fault("the kernel refused a Nat numeral that is too large");
                }
                return Ok(Some(self.store.mk_nat(&r)));
            }
            return Ok(None);
        }
        let Term::App(f1, a1) = self.store.get(f) else { return Ok(None) };
        let Term::Const(n, ls) = self.store.get(f1) else { return Ok(None) };
        if !self.store.levels(ls).is_empty() {
            return Ok(None);
        }
        let b = &self.env.builtins;
        let which = if Some(n) == b.nat_add {
            0
        } else if Some(n) == b.nat_sub {
            1
        } else if Some(n) == b.nat_mul {
            2
        } else if Some(n) == b.nat_pow {
            3
        } else if Some(n) == b.nat_gcd {
            4
        } else if Some(n) == b.nat_mod {
            5
        } else if Some(n) == b.nat_div {
            6
        } else if Some(n) == b.nat_beq {
            7
        } else if Some(n) == b.nat_ble {
            8
        } else if Some(n) == b.nat_land {
            9
        } else if Some(n) == b.nat_lor {
            10
        } else if Some(n) == b.nat_xor {
            11
        } else if Some(n) == b.nat_shift_left {
            12
        } else if Some(n) == b.nat_shift_right {
            13
        } else {
            return Ok(None);
        };
        let res_bool = which == 7 || which == 8;
        if !self.nat_builtin_ok(n, 2, res_bool) {
            return Ok(None);
        }
        let x = self.whnf(a1)?;
        let Some(xv) = self.nat_lit_value(x) else { return Ok(None) };
        let y = self.whnf(a)?;
        let Some(yv) = self.nat_lit_value(y) else { return Ok(None) };
        let r = match which {
            0 => xv.add(&yv),
            1 => xv.sub(&yv),
            2 => xv.mul(&yv),
            3 => {
                let Some(k) = yv.to_u64().filter(|&k| k <= MAX_COUNT) else { return Ok(None) };
                if xv > BigNat::from_u64(1) && k != 0 && xv.bit_len().saturating_mul(k) > MAX_NAT_BITS {
                    return fault("the kernel refused Nat.pow: result too large");
                }
                xv.pow(k)
            }
            4 => xv.gcd(&yv),
            5 => xv.rem(&yv),
            6 => xv.div(&yv),
            7 => return Ok(self.mk_bool_const(xv == yv)),
            8 => return Ok(self.mk_bool_const(xv <= yv)),
            9 => xv.and(&yv),
            10 => xv.or(&yv),
            11 => xv.xor(&yv),
            12 => {
                if xv.is_zero() {
                    return Ok(Some(self.store.mk_nat(&xv)));
                }
                let Some(k) = yv.to_u64().filter(|&k| k <= MAX_COUNT) else {
                    return fault("the kernel refused Nat.shiftLeft: shift too large");
                };
                if xv.bit_len().saturating_add(k) > MAX_NAT_BITS {
                    return fault("the kernel refused Nat.shiftLeft: result too large");
                }
                xv.shl(k)
            }
            _ => match yv.to_u64() {
                Some(k) => xv.shr(k),
                None => BigNat::zero(),
            },
        };
        if r.bit_len() > MAX_NAT_BITS {
            return fault("the kernel refused a Nat numeral that is too large");
        }
        Ok(Some(self.store.mk_nat(&r)))
    }

    /// Weak head normal form (with delta and literal extensions).
    pub fn whnf(&mut self, t: TermId) -> R<TermId> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return fault("recursion depth exceeded");
        }
        let r = self.whnf_inner(t);
        self.depth -= 1;
        r
    }

    fn whnf_inner(&mut self, t: TermId) -> R<TermId> {
        self.stats[2] += 1;
        match self.store.get(t) {
            Term::BVar(_) | Term::Sort(_) | Term::Pi(..) | Term::Nat(_) | Term::Str(_) | Term::Local(_) => return Ok(t),
            _ => {}
        }
        if let Some(r) = self.whnf_c.get(t) {
            return Ok(r);
        }
        let mut cur = t;
        loop {
            let t1 = self.whnf_core(cur, false, false)?;
            if let Some(v) = self.reduce_nat(t1)? {
                self.whnf_c.insert(t, v);
                return Ok(v);
            }
            match self.unfold_definition(t1)? {
                Some(next) => cur = next,
                None => {
                    self.whnf_c.insert(t, t1);
                    return Ok(t1);
                }
            }
        }
    }

    // ----- definitional equality -------------------------------------------------

    fn levels_eq(&mut self, a: LevelsId, b: LevelsId) -> bool {
        let xa = self.store.levels(a).to_vec();
        let xb = self.store.levels(b).to_vec();
        if xa.len() != xb.len() {
            return false;
        }
        for (x, y) in xa.into_iter().zip(xb) {
            if !self.store.level_eq(x, y) {
                return false;
            }
        }
        true
    }

    /// `is_def_eq`: definitional equality of two closed terms.
    pub fn is_def_eq(&mut self, t: TermId, s: TermId) -> R<bool> {
        let r = self.is_def_eq_core(t, s)?;
        let key = ordered(t, s);
        if r {
            self.success.insert(key);
        } else if !self.eager_reduce {
            self.failure.insert(key);
        }
        Ok(r)
    }

    fn quick_is_def_eq(&mut self, t: TermId, s: TermId) -> R<Option<bool>> {
        if t == s || self.success.contains(&ordered(t, s)) {
            return Ok(Some(true));
        }
        match (self.store.get(t), self.store.get(s)) {
            (Term::Lam(..), Term::Lam(..)) | (Term::Pi(..), Term::Pi(..)) => Ok(Some(self.is_def_eq_binding(t, s)?)),
            (Term::Sort(a), Term::Sort(b)) => Ok(Some(self.store.level_eq(a, b))),
            (Term::Nat(a), Term::Nat(b)) => Ok(Some(self.store.nat_value(a) == self.store.nat_value(b))),
            (Term::Str(a), Term::Str(b)) => Ok(Some(self.env.raw.strs[a as usize] == self.env.raw.strs[b as usize])),
            (Term::Nat(_), Term::Str(_)) | (Term::Str(_), Term::Nat(_)) => Ok(Some(false)),
            _ => Ok(None),
        }
    }

    fn is_def_eq_binding(&mut self, t0: TermId, s0: TermId) -> R<bool> {
        let k = self.store.get(t0);
        let same = |x: Term| std::mem::discriminant(&x) == std::mem::discriminant(&k);
        let base = self.store.local_ub(t0).max(self.store.local_ub(s0));
        let mut next = base;
        let dummy = {
            let z = self.store.mk_zero();
            self.store.mk_sort(z)
        };
        let mut subst: Vec<TermId> = Vec::new();
        let (mut t, mut s) = (t0, s0);
        loop {
            let (dt, bt) = match self.store.get(t) {
                Term::Lam(d, b) | Term::Pi(d, b) => (d, b),
                _ => return fault("is_def_eq_binding"),
            };
            let (ds, bs) = match self.store.get(s) {
                Term::Lam(d, b) | Term::Pi(d, b) => (d, b),
                _ => return fault("is_def_eq_binding"),
            };
            let mut s_ty: Option<TermId> = None;
            if dt != ds {
                let st = self.store.instantiate(ds, &subst);
                let tt = self.store.instantiate(dt, &subst);
                if !self.is_def_eq(tt, st)? {
                    return Ok(false);
                }
                s_ty = Some(st);
            }
            if self.store.lbr(bt) > 0 || self.store.lbr(bs) > 0 {
                let st = match s_ty {
                    Some(x) => x,
                    None => self.store.instantiate(ds, &subst),
                };
                let x = self.fresh_local(&mut next, st);
                subst.push(x);
            } else {
                subst.push(dummy);
            }
            t = bt;
            s = bs;
            if !(same(self.store.get(t)) && same(self.store.get(s))) {
                break;
            }
        }
        let ti = self.store.instantiate(t, &subst);
        let si = self.store.instantiate(s, &subst);
        self.is_def_eq(ti, si)
    }

    fn is_def_eq_args(&mut self, t: TermId, s: TermId) -> R<bool> {
        let (mut t, mut s) = (t, s);
        loop {
            match (self.store.get(t), self.store.get(s)) {
                (Term::App(f1, a1), Term::App(f2, a2)) => {
                    if !self.is_def_eq(a1, a2)? {
                        return Ok(false);
                    }
                    t = f1;
                    s = f2;
                }
                _ => break,
            }
        }
        Ok(!matches!(self.store.get(t), Term::App(..)) && !matches!(self.store.get(s), Term::App(..)))
    }

    fn try_eta_expansion_core(&mut self, t: TermId, s: TermId) -> R<bool> {
        if !matches!(self.store.get(t), Term::Lam(..)) || matches!(self.store.get(s), Term::Lam(..)) {
            return Ok(false);
        }
        let st0 = self.infer(s, false)?;
        let st = self.whnf(st0)?;
        let Term::Pi(d, _) = self.store.get(st) else { return Ok(false) };
        let b0 = self.store.mk_bvar(0);
        let app = self.store.mk_app(s, b0);
        let new_s = self.store.mk_lam(d, app);
        self.is_def_eq(t, new_s)
    }

    fn try_eta_expansion(&mut self, t: TermId, s: TermId) -> R<bool> {
        Ok(self.try_eta_expansion_core(t, s)? || self.try_eta_expansion_core(s, t)?)
    }

    fn try_eta_struct_core(&mut self, t: TermId, s: TermId) -> R<bool> {
        let sf = self.store.app_fn(s);
        let Term::Const(sn, _) = self.store.get(sf) else { return Ok(false) };
        let Some(info) = self.const_info_opt(sn) else { return Ok(false) };
        let ConstKind::Ctor(sc) = &info.kind else { return Ok(false) };
        let sc: CtorInfo = *sc;
        if !self.is_non_rec_structure(sc.induct) {
            return Ok(false);
        }
        let tt = self.infer(t, false)?;
        let mut s_type = self.infer(s, false)?;
        if !self.is_def_eq(tt, s_type)? {
            return Ok(false);
        }
        let num_ctor_args = sc.num_params as usize + sc.num_fields as usize;
        let (mut t, mut s) = (t, s);
        let mut s_args = Vec::new();
        self.store.unfold_app(s, &mut s_args);
        if s_args.len() < num_ctor_args {
            let mut next = self.store.local_ub(t).max(self.store.local_ub(s));
            let mut fvars = Vec::new();
            while let Term::Pi(d, b) = self.store.get(s_type) {
                let x = self.fresh_local(&mut next, d);
                fvars.push(x);
                s_type = self.store.instantiate(b, &[x]);
            }
            t = self.store.mk_app_n(t, &fvars);
            s = self.store.mk_app_n(s, &fvars);
            s_args.clear();
            self.store.unfold_app(s, &mut s_args);
        }
        if s_args.len() != num_ctor_args {
            return Ok(false);
        }
        let np = sc.num_params as usize;
        for i in np..s_args.len() {
            let proj = self.store.mk_proj(sc.induct, (i - np) as u32, t);
            if !self.is_def_eq(proj, s_args[i])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn try_eta_struct(&mut self, t: TermId, s: TermId) -> R<bool> {
        Ok(self.try_eta_struct_core(t, s)? || self.try_eta_struct_core(s, t)?)
    }

    fn is_def_eq_app(&mut self, t: TermId, s: TermId) -> R<bool> {
        if !matches!(self.store.get(t), Term::App(..)) || !matches!(self.store.get(s), Term::App(..)) {
            return Ok(false);
        }
        let mut ta = Vec::new();
        let tf = self.store.unfold_app(t, &mut ta);
        let mut sa = Vec::new();
        let sf = self.store.unfold_app(s, &mut sa);
        if !self.is_def_eq(tf, sf)? || ta.len() != sa.len() {
            return Ok(false);
        }
        for i in 0..ta.len() {
            if !self.is_def_eq(ta[i], sa[i])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_def_eq_proof_irrel(&mut self, t: TermId, s: TermId) -> R<Option<bool>> {
        let tt = self.infer(t, false)?;
        if !self.is_prop(tt)? {
            return Ok(None);
        }
        let st = self.infer(s, false)?;
        Ok(Some(self.is_def_eq(tt, st)?))
    }

    fn failed_before(&self, t: TermId, s: TermId) -> bool {
        self.failure.contains(&ordered(t, s))
    }

    fn cache_failure(&mut self, t: TermId, s: TermId) {
        self.failure.insert(ordered(t, s));
    }

    fn try_unfold_proj_app(&mut self, e: TermId) -> R<Option<TermId>> {
        let f = self.store.app_fn(e);
        if let Term::Proj(..) = self.store.get(f) {
            let en = self.whnf_core(e, false, false)?;
            if en != e {
                return Ok(Some(en));
            }
        }
        Ok(None)
    }

    /// One lazy delta step (`lazy_delta_reduction_step`). Updates `tn` and `sn`.
    pub(crate) fn lazy_delta_reduction_step(&mut self, tn: &mut TermId, sn: &mut TermId) -> R<Status> {
        let dt = self.is_delta(*tn);
        let ds = self.is_delta(*sn);
        match (dt, ds) {
            (None, None) => return Ok(Status::DefUnknown),
            (Some(_), None) => {
                if let Some(s2) = self.try_unfold_proj_app(*sn)? {
                    *sn = s2;
                } else {
                    let Some(u) = self.unfold_definition(*tn)? else { return Ok(Status::DefUnknown) };
                    *tn = self.whnf_core(u, false, true)?;
                }
            }
            (None, Some(_)) => {
                if let Some(t2) = self.try_unfold_proj_app(*tn)? {
                    *tn = t2;
                } else {
                    let Some(u) = self.unfold_definition(*sn)? else { return Ok(Status::DefUnknown) };
                    *sn = self.whnf_core(u, false, true)?;
                }
            }
            (Some((nt, ht)), Some((ns, hs))) => {
                let c = compare_hints(ht, hs);
                if c < 0 {
                    let Some(u) = self.unfold_definition(*tn)? else { return Ok(Status::DefUnknown) };
                    *tn = self.whnf_core(u, false, true)?;
                } else if c > 0 {
                    let Some(u) = self.unfold_definition(*sn)? else { return Ok(Status::DefUnknown) };
                    *sn = self.whnf_core(u, false, true)?;
                } else {
                    if matches!(self.store.get(*tn), Term::App(..))
                        && matches!(self.store.get(*sn), Term::App(..))
                        && nt == ns
                        && matches!(ht, Hints::Regular(_))
                        && !self.failed_before(*tn, *sn)
                    {
                        let lt = match self.store.get(self.store.app_fn(*tn)) {
                            Term::Const(_, l) => l,
                            _ => 0,
                        };
                        let ls = match self.store.get(self.store.app_fn(*sn)) {
                            Term::Const(_, l) => l,
                            _ => 0,
                        };
                        let (a, b) = (*tn, *sn);
                        if self.levels_eq(lt, ls) && self.is_def_eq_args(a, b)? {
                            return Ok(Status::DefEqual);
                        }
                        self.cache_failure(a, b);
                    }
                    let Some(u1) = self.unfold_definition(*tn)? else { return Ok(Status::DefUnknown) };
                    let Some(u2) = self.unfold_definition(*sn)? else { return Ok(Status::DefUnknown) };
                    *tn = self.whnf_core(u1, false, true)?;
                    *sn = self.whnf_core(u2, false, true)?;
                }
            }
        }
        Ok(match self.quick_is_def_eq(*tn, *sn)? {
            Some(true) => Status::DefEqual,
            Some(false) => Status::DefDiff,
            None => Status::Continue,
        })
    }

    fn is_def_eq_offset(&mut self, t: TermId, s: TermId) -> R<Option<bool>> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Some(true));
        }
        let pt = self.is_nat_succ(t);
        let ps = self.is_nat_succ(s);
        if let (Some(a), Some(b)) = (pt, ps) {
            return Ok(Some(self.is_def_eq_core(a, b)?));
        }
        Ok(None)
    }

    fn is_nat_zero(&self, t: TermId) -> bool {
        match self.store.get(t) {
            Term::Nat(id) => self.store.nat_value(id).is_zero(),
            Term::Const(n, ls) => Some(n) == self.env.builtins.nat_zero && self.store.levels(ls).is_empty(),
            _ => false,
        }
    }

    fn is_nat_succ(&mut self, t: TermId) -> Option<TermId> {
        match self.store.get(t) {
            Term::Nat(id) => {
                let v = self.store.nat_value(id);
                if v.is_zero() {
                    None
                } else {
                    let p = v.pred();
                    Some(self.store.mk_nat(&p))
                }
            }
            Term::App(f, a) => match self.store.get(f) {
                Term::Const(n, ls) if Some(n) == self.env.builtins.nat_succ && self.store.levels(ls).is_empty() => Some(a),
                _ => None,
            },
            _ => None,
        }
    }

    /// `lazy_delta_reduction`: `None` means undetermined.
    fn lazy_delta_reduction(&mut self, tn: &mut TermId, sn: &mut TermId) -> R<Option<bool>> {
        loop {
            if let Some(r) = self.is_def_eq_offset(*tn, *sn)? {
                return Ok(Some(r));
            }
            let no_locals = self.store.local_ub(*tn) == 0 && self.store.local_ub(*sn) == 0;
            if no_locals || self.eager_reduce {
                if let Some(tv) = self.reduce_nat(*tn)? {
                    return Ok(Some(self.is_def_eq_core(tv, *sn)?));
                } else if let Some(sv) = self.reduce_nat(*sn)? {
                    return Ok(Some(self.is_def_eq_core(*tn, sv)?));
                }
            }
            match self.lazy_delta_reduction_step(tn, sn)? {
                Status::Continue => {}
                Status::DefUnknown => return Ok(None),
                Status::DefEqual => return Ok(Some(true)),
                Status::DefDiff => return Ok(Some(false)),
            }
        }
    }

    fn lazy_delta_proj_reduction(&mut self, tc: &mut TermId, sc: &mut TermId, sname: NameId, idx: u32) -> R<bool> {
        loop {
            match self.lazy_delta_reduction_step(tc, sc)? {
                Status::Continue => {}
                Status::DefEqual => return Ok(true),
                Status::DefUnknown | Status::DefDiff => {
                    if let Some(t) = self.reduce_proj_core(*tc, sname, idx)? {
                        if let Some(s) = self.reduce_proj_core(*sc, sname, idx)? {
                            return self.is_def_eq_core(t, s);
                        }
                    }
                    return self.is_def_eq_core(*tc, *sc);
                }
            }
        }
    }

    fn try_string_lit_expansion_core(&mut self, t: TermId, s: TermId) -> R<Option<bool>> {
        if !matches!(self.store.get(t), Term::Str(_)) {
            return Ok(None);
        }
        let Term::App(f, _) = self.store.get(s) else { return Ok(None) };
        let Term::Const(n, _) = self.store.get(f) else { return Ok(None) };
        if Some(n) != self.env.builtins.string_of_list {
            return Ok(None);
        }
        let k = self.string_lit_to_constructor(t)?;
        let w = self.whnf(k)?;
        Ok(Some(self.is_def_eq_core(w, s)?))
    }

    fn try_string_lit_expansion(&mut self, t: TermId, s: TermId) -> R<Option<bool>> {
        if let Some(r) = self.try_string_lit_expansion_core(t, s)? {
            return Ok(Some(r));
        }
        self.try_string_lit_expansion_core(s, t)
    }

    /// `is_unit_like` of type_checker.cpp: a non-recursive structure whose fields are propositions or unit-like.
    fn is_unit_like(&mut self, t: TermId) -> R<bool> {
        let mut next = self.store.local_ub(t);
        let mut cur = self.whnf(t)?;
        while let Term::Pi(d, b) = self.store.get(cur) {
            let x = self.fresh_local(&mut next, d);
            let bi = self.store.instantiate(b, &[x]);
            cur = self.whnf(bi)?;
        }
        let mut iargs = Vec::new();
        let head = self.store.unfold_app(cur, &mut iargs);
        let Term::Const(iname, ils) = self.store.get(head) else { return Ok(false) };
        if !self.is_non_rec_structure(iname) {
            return Ok(false);
        }
        let Some(info) = self.const_info_opt(iname) else { return Ok(false) };
        let ConstKind::Induct(iv) = &info.kind else { return Ok(false) };
        let Some(&ctor) = iv.ctors.first() else { return Ok(false) };
        let mut ct = self.const_type(ctor, ils)?;
        for _ in 0..iargs.len() {
            match self.store.get(ct) {
                Term::Pi(_, b) => ct = b,
                _ => return Ok(false),
            }
        }
        ct = self.store.instantiate(ct, &iargs);
        while let Term::Pi(d, b) = self.store.get(ct) {
            if !self.is_prop(d)? && !self.is_unit_like(d)? {
                return Ok(false);
            }
            let x = self.fresh_local(&mut next, d);
            let bi = self.store.instantiate(b, &[x]);
            ct = self.whnf(bi)?;
        }
        Ok(true)
    }

    fn is_def_eq_unit_like(&mut self, t: TermId, s: TermId) -> R<bool> {
        let tt0 = self.infer(t, false)?;
        let tt = self.whnf(tt0)?;
        if !self.is_unit_like(tt)? {
            return Ok(false);
        }
        let st = self.infer(s, false)?;
        self.is_def_eq_core(tt, st)
    }

    fn is_def_eq_core(&mut self, t: TermId, s: TermId) -> R<bool> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return fault("recursion depth exceeded");
        }
        let r = self.is_def_eq_core_inner(t, s);
        self.depth -= 1;
        r
    }

    fn is_def_eq_core_inner(&mut self, t: TermId, s: TermId) -> R<bool> {
        self.stats[3] += 1;
        if let Some(r) = self.quick_is_def_eq(t, s)? {
            return Ok(r);
        }
        if let Some(bt) = self.env.builtins.bool_true {
            let s_is_true = matches!(self.store.get(s), Term::Const(n, ls) if n == bt && self.store.levels(ls).is_empty());
            if s_is_true && (self.store.local_ub(t) == 0 || self.eager_reduce) {
                let wt = self.whnf(t)?;
                if matches!(self.store.get(wt), Term::Const(n, ls) if n == bt && self.store.levels(ls).is_empty()) {
                    return Ok(true);
                }
            }
        }
        if let Some(r) = self.is_def_eq_proof_irrel(t, s)? {
            return Ok(r);
        }
        let mut tn = self.whnf_core(t, false, true)?;
        let mut sn = self.whnf_core(s, false, true)?;
        if tn != t || sn != s {
            if let Some(r) = self.quick_is_def_eq(tn, sn)? {
                return Ok(r);
            }
        }
        if let Some(r) = self.lazy_delta_reduction(&mut tn, &mut sn)? {
            return Ok(r);
        }
        if let (Term::Const(a, la), Term::Const(b, lb)) = (self.store.get(tn), self.store.get(sn)) {
            if a == b && self.levels_eq(la, lb) {
                return Ok(true);
            }
        }
        if let (Term::Proj(sa, ia, ca), Term::Proj(sb, ib, cb)) = (self.store.get(tn), self.store.get(sn)) {
            if sa == sb && ia == ib {
                let (mut tc, mut sc) = (ca, cb);
                if self.lazy_delta_proj_reduction(&mut tc, &mut sc, sa, ia)? {
                    return Ok(true);
                }
            }
        }
        let tnn = self.whnf_core(tn, false, false)?;
        let snn = self.whnf_core(sn, false, false)?;
        if tnn != tn || snn != sn {
            return self.is_def_eq_core(tnn, snn);
        }
        if self.is_def_eq_app(tn, sn)? {
            return Ok(true);
        }
        if self.try_eta_expansion(tn, sn)? {
            return Ok(true);
        }
        if self.try_eta_struct(tn, sn)? {
            return Ok(true);
        }
        if let Some(r) = self.try_string_lit_expansion(tn, sn)? {
            return Ok(r);
        }
        if self.is_def_eq_unit_like(tn, sn)? {
            return Ok(true);
        }
        Ok(false)
    }

    // ----- declarations ----------------------------------------------------------

    /// Rejects a level parameter of `t` that is not in `params` (M4).
    pub fn check_levels_declared(&mut self, t: TermId, params: &[NameId]) -> R<()> {
        let mut stack = vec![t];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !self.store.has_param(x) || !seen.insert(x) {
                continue;
            }
            match self.store.get(x) {
                Term::Sort(l) => self.check_level_declared(l, params)?,
                Term::Const(_, ls) => {
                    for l in self.store.levels(ls).to_vec() {
                        self.check_level_declared(l, params)?;
                    }
                }
                Term::App(a, b) | Term::Lam(a, b) | Term::Pi(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                Term::Let(a, b, c) => {
                    stack.push(a);
                    stack.push(b);
                    stack.push(c);
                }
                Term::Proj(_, _, e) => stack.push(e),
                _ => {}
            }
        }
        Ok(())
    }

    fn check_level_declared(&mut self, l: LevelId, params: &[NameId]) -> R<()> {
        if !self.store.level_has_param(l) {
            return Ok(());
        }
        match self.store.level(l) {
            Level::Zero => Ok(()),
            Level::Succ(a) => self.check_level_declared(a, params),
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.check_level_declared(a, params)?;
                self.check_level_declared(b, params)
            }
            Level::Param(n) => {
                if params.contains(&n) {
                    Ok(())
                } else {
                    reject(format!("undefined universe level parameter '{}'", self.env.raw.name_to_string(n)))
                }
            }
        }
    }

    /// Checks the declaration at file position `pos` (P6: its constants must be earlier).
    pub fn check_decl(&mut self, pos: u32) -> R<()> {
        self.pos = pos;
        self.allow_block = false;
        self.eager_reduce = false;
        let env = self.env;
        let Some(decl) = env.raw.decls.get(pos as usize) else { return reject("no declaration at this position") };
        match decl {
            Decl::Axiom { name } => {
                let info = self.own_info(*name, pos)?;
                self.check_header(info)?;
                Ok(())
            }
            Decl::Def { name } => {
                let info = self.own_info(*name, pos)?;
                let ConstKind::Def { value, safety, .. } = &info.kind else { return reject("declaration kind mismatch") };
                if *safety != Safety::Safe {
                    return Ok(());
                }
                let ty = self.check_header(info)?;
                self.check_value(*value, ty, info)
            }
            Decl::Thm { name } => {
                let info = self.own_info(*name, pos)?;
                let ConstKind::Thm { value, .. } = &info.kind else { return reject("declaration kind mismatch") };
                let ty = self.check_header(info)?;
                if !self.is_prop(ty)? {
                    return reject("theorem type is not a proposition");
                }
                self.check_value(*value, ty, info)
            }
            Decl::Opaque { name } => {
                let info = self.own_info(*name, pos)?;
                let ConstKind::Opaque { value, .. } = &info.kind else { return reject("declaration kind mismatch") };
                if info.is_unsafe {
                    return Ok(());
                }
                let ty = self.check_header(info)?;
                self.check_value(*value, ty, info)
            }
            Decl::Quot { name } => crate::quot::check_quot(self, pos, *name),
            Decl::Inductive { types, ctors, recs } => {
                self.clear_def_caches();
                let r = crate::inductive::check_inductive(self, pos, types, ctors, recs);
                self.clear_def_caches();
                r
            }
        }
    }

    /// The constant declared by the declaration at `pos` (must have been declared there).
    fn own_info(&self, name: NameId, pos: u32) -> R<&'e ConstInfo> {
        let env = self.env;
        match env.get(name) {
            Some(i) if i.pos == pos => Ok(i),
            _ => reject("declaration does not match the constant table"),
        }
    }

    /// Universe parameters are distinct and declared; the type is closed and a type.
    fn check_header(&mut self, info: &'e ConstInfo) -> R<TermId> {
        for (i, p) in info.level_params.iter().enumerate() {
            if info.level_params[..i].contains(p) {
                return reject("duplicate universe parameter");
            }
        }
        let ty = self.import_expr(info.ty);
        if self.store.lbr(ty) > 0 {
            return reject("loose bound variable in type");
        }
        self.check_levels_declared(ty, &info.level_params)?;
        let s = self.infer(ty, true)?;
        self.ensure_sort(s)?;
        Ok(ty)
    }

    fn check_value(&mut self, value: RawExpr, ty: TermId, info: &'e ConstInfo) -> R<()> {
        let v = self.import_expr(value);
        if self.store.lbr(v) > 0 {
            return reject("loose bound variable in value");
        }
        self.check_levels_declared(v, &info.level_params)?;
        let vt = self.infer(v, true)?;
        if !self.is_def_eq(vt, ty)? {
            return reject("declaration type mismatch");
        }
        Ok(())
    }

    /// The inductive info of `n` if it is a visible inductive type (helper for inductive.rs).
    pub fn induct_info(&self, n: NameId) -> Option<&'e InductInfo> {
        match &self.const_info_opt(n)?.kind {
            ConstKind::Induct(iv) => Some(iv),
            _ => None,
        }
    }
}

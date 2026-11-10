//! Inductive blocks (docs/CHECKER.md section 3, rules I1-I5).
//!
//! Port of `add_inductive_fn` and `elim_nested_inductive_fn` from the reference kernel
//! (`inductive.cpp`), in "derive and compare" form: the block is reconstructed from the
//! file's types and constructors, every derived fact (flags, recursor types, recursor rules,
//! `k`, elimination level) is computed here, and each one is compared with the file's data.
//! Nothing taken from the file's recursors drives the derivation.
//!
//! Typing: the checker (`tc`) only ever sees terms over the real constants. Nested occurrences
//! `J Ds is` are replaced by block-local auxiliary constants (fresh ids >= `names.len()`) only in
//! the structural part (`aux` views): positivity, the valid-application test and the recursor
//! generation. Every term that leaves that part is translated back (`restore`) before it is
//! closed over locals, and no term containing an auxiliary constant is ever typed or compared.

use crate::env::{ConstKind, NameNode, NameId};
use crate::store::{LevelId, LevelsId, Term, TermId};
use crate::tc::{reject, Checker, R};
use crate::util::{FxHashMap, FxHashSet};

/// What an auxiliary constant stands for when translating back (`restore_nested`).
#[derive(Clone, Copy)]
enum Restore {
    /// Auxiliary inductive type standing for the nested occurrence `key` (`J Ds`).
    Ind(TermId),
    /// Auxiliary constructor of the type with key `key`, standing for the real constructor.
    Ctor(TermId, NameId),
    /// Auxiliary recursor, standing for the real recursor with the given name.
    Rec(NameId),
}

/// One type of the (possibly extended) block.
struct TyD {
    /// The real name, or a fresh auxiliary id.
    name: NameId,
    /// Type after the parameters, over the block's parameter locals (contains only indices).
    ty: TermId,
    /// Number of indices.
    nidx: usize,
    ctors: Vec<CtorD>,
}

struct CtorD {
    /// Name used in terms: the real name, or a fresh auxiliary id.
    name: NameId,
    /// The real constructor name (for rules).
    real: NameId,
    /// Type after the parameters, before nested replacement (typed by the checker).
    pre: TermId,
    /// Type after the parameters, with nested occurrences replaced (structural view).
    res: TermId,
    /// Number of fields.
    nfields: usize,
    /// Full closed type (original types only; `None` for auxiliary constructors).
    full: Option<TermId>,
}

/// Per type, the locals of its recursor.
struct IndRec {
    c: TermId,
    indices: Vec<TermId>,
    major: TermId,
}

/// Per constructor, the locals used by its minor premise.
struct CtorRec {
    b_u: Vec<TermId>,
    us: Vec<UData>,
    minor: TermId,
}

struct UData {
    u: TermId,
    xs: Vec<TermId>,
    it_idx: usize,
    it_indices: Vec<TermId>,
}

/// A derived recursor, to be compared with the file's.
struct DerivedRec {
    lparams: Vec<NameId>,
    ty: TermId,
    nidx: usize,
    rules: Vec<(NameId, usize, TermId)>,
}

struct Blk {
    lvl_ids: Vec<LevelId>,
    levels: LevelsId,
    np: usize,
    orig_names: Vec<NameId>,
    tys: Vec<TyD>,
    params: Vec<TermId>,
    ind_cnst: Vec<TermId>,
    result_level: LevelId,
    next_depth: u32,
    fake_base: u32,
    fake_next: u32,
    /// Every type name of the block so far (real and auxiliary).
    names: FxHashSet<NameId>,
    /// Key (`J Ds` over the parameters) and auxiliary name of each auxiliary type.
    aux_keys: Vec<(TermId, NameId)>,
    restore: FxHashMap<NameId, Restore>,
}

pub fn check_inductive(tc: &mut Checker, pos: u32, types: &[NameId], ctors: &[NameId], recs: &[NameId]) -> R<()> {
    let saved = tc.allow_block;
    tc.allow_block = true;
    let r = check_block(tc, pos, types, ctors, recs);
    tc.allow_block = saved;
    r
}

fn has_dup(xs: &[NameId]) -> bool {
    let mut v = xs.to_vec();
    v.sort_unstable();
    v.windows(2).any(|w| w[0] == w[1])
}

fn local_type(tc: &Checker, x: TermId) -> TermId {
    match tc.store.get(x) {
        Term::Local(l) => tc.store.local_type(l),
        _ => x,
    }
}

/// Is `p` a prefix (possibly equal) of the name `n`?
fn name_has_prefix(tc: &Checker, n: NameId, p: NameId) -> bool {
    let names = &tc.env.raw.names;
    let mut cur = n;
    loop {
        if cur == p {
            return true;
        }
        match names.get(cur as usize) {
            Some(NameNode::Str(pp, _)) | Some(NameNode::Num(pp, _)) => cur = *pp,
            _ => return false,
        }
    }
}

/// The name of the recursor `prefix.comp` among the block's declared recursors.
fn find_rec(tc: &Checker, recs: &[NameId], prefix: NameId, comp: &str) -> Option<NameId> {
    recs.iter().copied().find(|&r| match tc.env.raw.names.get(r as usize) {
        Some(NameNode::Str(p, s)) => *p == prefix && &**s == comp,
        _ => false,
    })
}

fn spine(tc: &Checker, t: TermId) -> (TermId, Vec<TermId>) {
    let mut args = Vec::new();
    let h = tc.store.unfold_app(t, &mut args);
    (h, args)
}

/// Opens the first `np` binders of the syntactic Pi chain `t` (checking they exist), instantiates
/// them with `xs` and returns the residual together with the number of remaining binders.
fn strip_params(tc: &mut Checker, t: TermId, xs: &[TermId]) -> R<(TermId, usize)> {
    let mut cur = t;
    for _ in 0..xs.len() {
        match tc.store.get(cur) {
            Term::Pi(_, b) => cur = b,
            _ => return reject("inductive type has fewer parameters than declared"),
        }
    }
    let r = tc.store.instantiate(cur, xs);
    let mut nfields = 0usize;
    let mut c = r;
    while let Term::Pi(_, b) = tc.store.get(c) {
        nfields += 1;
        c = b;
    }
    Ok((r, nfields))
}

/// Counts the leading Pi binders of `t` after `np` (the fields of a constructor residual).
fn count_pis(tc: &Checker, t: TermId) -> usize {
    let mut n = 0;
    let mut c = t;
    while let Term::Pi(_, b) = tc.store.get(c) {
        n += 1;
        c = b;
    }
    n
}

impl Blk {
    fn fresh(&mut self, tc: &mut Checker, ty: TermId) -> TermId {
        tc.fresh_local(&mut self.next_depth, ty)
    }

    fn fake(&mut self) -> NameId {
        let id = self.fake_base + self.fake_next;
        self.fake_next += 1;
        id
    }

    fn has_ind_occ(&self, tc: &Checker, t: TermId) -> bool {
        let mut stack = vec![t];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match tc.store.get(x) {
                Term::Const(n, _) => {
                    if self.names.contains(&n) {
                        return true;
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
        false
    }

    /// `t` is `I As is` for the block type `I` at index `i` (rule `is_valid_ind_app`).
    fn is_valid_ind_app(&self, tc: &Checker, t: TermId, i: usize) -> bool {
        let (head, args) = spine(tc, t);
        let Some(&cst) = self.ind_cnst.get(i) else { return false };
        if head != cst {
            return false;
        }
        let np = self.np;
        let nidx = self.tys[i].nidx;
        if args.len() != np + nidx {
            return false;
        }
        if args[..np] != self.params[..] {
            return false;
        }
        args[np..].iter().all(|&a| !self.has_ind_occ(tc, a))
    }

    fn valid_ind_app_any(&self, tc: &Checker, t: TermId) -> Option<usize> {
        (0..self.tys.len()).find(|&i| self.is_valid_ind_app(tc, t, i))
    }

    /// `(i, indices)` of an `I As is` application; reject if `t` is not one.
    fn i_indices(&self, tc: &Checker, t: TermId) -> R<(usize, Vec<TermId>)> {
        let Some(i) = self.valid_ind_app_any(tc, t) else {
            return reject("constructor result is not a valid application of the block");
        };
        let (_, args) = spine(tc, t);
        Ok((i, args[self.np..].to_vec()))
    }

    /// `is_rec_argument`: the index of the block type a field of type `t` recursively refers to.
    fn is_rec_argument(&mut self, tc: &mut Checker, t: TermId) -> R<Option<usize>> {
        let mut t = tc.whnf(t)?;
        while let Term::Pi(d, b) = tc.store.get(t) {
            let x = self.fresh(tc, d);
            let body = tc.store.instantiate(b, &[x]);
            t = tc.whnf(body)?;
        }
        Ok(self.valid_ind_app_any(tc, t))
    }

    /// `check_positivity`.
    fn check_positivity(&mut self, tc: &mut Checker, t: TermId) -> R<()> {
        let t = tc.whnf(t)?;
        if !self.has_ind_occ(tc, t) {
            return Ok(());
        }
        match tc.store.get(t) {
            Term::Pi(d, b) => {
                if self.has_ind_occ(tc, d) {
                    return reject("non positive occurrence of the datatypes being declared");
                }
                let x = self.fresh(tc, d);
                let body = tc.store.instantiate(b, &[x]);
                self.check_positivity(tc, body)
            }
            _ => {
                if self.valid_ind_app_any(tc, t).is_some() {
                    Ok(())
                } else {
                    reject("non valid occurrence of the datatypes being declared")
                }
            }
        }
    }

    /// Opens the fields of the closed residual `t0` with fresh locals; returns the fields with
    /// their sort levels and the final type. Typing happens on `t0` itself.
    fn typed_fields(&mut self, tc: &mut Checker, t0: TermId) -> R<(Vec<(TermId, LevelId)>, TermId)> {
        let mut out = Vec::new();
        let mut t = t0;
        while let Term::Pi(d, b) = tc.store.get(t) {
            let s = tc.infer(d, true)?;
            let l = tc.ensure_sort(s)?;
            let x = self.fresh(tc, d);
            out.push((x, l));
            t = tc.store.instantiate(b, &[x]);
        }
        Ok((out, t))
    }

    /// Translates the auxiliary constants of `t` back to the nested occurrences and the real
    /// constructors and recursors (`restore_nested`). `t` must be closed over the parameter
    /// locals (no bound variables are abstracted yet), as the auxiliary applications refer to them.
    fn restore(&self, tc: &mut Checker, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> R<TermId> {
        if let Some(&r) = memo.get(&t) {
            return Ok(r);
        }
        let (head, args) = spine(tc, t);
        let matched = match tc.store.get(head) {
            Term::Const(n, lv) => self.restore.get(&n).copied().map(|r| (r, lv)),
            _ => None,
        };
        let r = match matched {
            Some((Restore::Rec(real), lv)) => {
                let h = tc.store.mk_const(real, lv);
                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    nargs.push(self.restore(tc, a, memo)?);
                }
                tc.store.mk_app_n(h, &nargs)
            }
            Some((Restore::Ind(key), _)) => {
                self.check_params_prefix(&args)?;
                tc.store.mk_app_n(key, &args[self.np..])
            }
            Some((Restore::Ctor(key, real), _)) => {
                self.check_params_prefix(&args)?;
                let mut kargs = Vec::new();
                let kh = tc.store.unfold_app(key, &mut kargs);
                let Term::Const(_, klv) = tc.store.get(kh) else {
                    return reject("failed to restore nested inductive types");
                };
                let h = tc.store.mk_const(real, klv);
                let h2 = tc.store.mk_app_n(h, &kargs);
                tc.store.mk_app_n(h2, &args[self.np..])
            }
            None => {
                if !args.is_empty() {
                    let h2 = if let Term::Const(..) = tc.store.get(head) { head } else { self.restore(tc, head, memo)? };
                    let mut nargs = Vec::with_capacity(args.len());
                    for a in args {
                        nargs.push(self.restore(tc, a, memo)?);
                    }
                    tc.store.mk_app_n(h2, &nargs)
                } else {
                    match tc.store.get(t) {
                        Term::Pi(d, b) => {
                            let d2 = self.restore(tc, d, memo)?;
                            let b2 = self.restore(tc, b, memo)?;
                            tc.store.mk_pi(d2, b2)
                        }
                        Term::Lam(d, b) => {
                            let d2 = self.restore(tc, d, memo)?;
                            let b2 = self.restore(tc, b, memo)?;
                            tc.store.mk_lam(d2, b2)
                        }
                        Term::Let(a, b, c) => {
                            let a2 = self.restore(tc, a, memo)?;
                            let b2 = self.restore(tc, b, memo)?;
                            let c2 = self.restore(tc, c, memo)?;
                            tc.store.mk_let(a2, b2, c2)
                        }
                        Term::Proj(s, i, e) => {
                            let e2 = self.restore(tc, e, memo)?;
                            tc.store.mk_proj(s, i, e2)
                        }
                        _ => t,
                    }
                }
            }
        };
        memo.insert(t, r);
        Ok(r)
    }

    fn check_params_prefix(&self, args: &[TermId]) -> R<()> {
        if args.len() < self.np || args[..self.np] != self.params[..] {
            return reject("failed to restore nested inductive types: auxiliary type not applied to the parameters");
        }
        Ok(())
    }

    /// Abstracts `xs` (locals) out of `body` and the domains of their types, producing a Pi or
    /// Lam term. Every domain and the body are restored first (`restore`), so the result is free of
    /// auxiliary constants.
    fn close(&self, tc: &mut Checker, xs: &[TermId], body: TermId, pi: bool) -> R<TermId> {
        let mut memo = FxHashMap::default();
        let body_r = self.restore(tc, body, &mut memo)?;
        let mut doms = Vec::with_capacity(xs.len());
        for &x in xs {
            let ty = local_type(tc, x);
            doms.push(self.restore(tc, ty, &mut memo)?);
        }
        let mut r = tc.store.abstract_locals(body_r, xs);
        for k in (0..xs.len()).rev() {
            let d = tc.store.abstract_locals(doms[k], &xs[..k]);
            r = if pi { tc.store.mk_pi(d, r) } else { tc.store.mk_lam(d, r) };
        }
        Ok(r)
    }

    /// `replace_if_nested` of the reference, on a closed (over locals) term.
    fn replace_if_nested(&mut self, tc: &mut Checker, e: TermId) -> R<Option<TermId>> {
        let Term::App(..) = tc.store.get(e) else { return Ok(None) };
        let (head, args) = spine(tc, e);
        let Term::Const(i_name, i_lvls) = tc.store.get(head) else { return Ok(None) };
        if self.names.contains(&i_name) {
            return Ok(None);
        }
        let Some(iv) = tc.induct_info(i_name) else { return Ok(None) };
        let inp = iv.num_params as usize;
        if inp > args.len() {
            return Ok(None);
        }
        let mut nested = false;
        let mut loose = false;
        for &a in &args[..inp] {
            if tc.store.lbr(a) > 0 {
                loose = true;
            }
            if self.has_ind_occ(tc, a) {
                nested = true;
            }
        }
        if !nested {
            return Ok(None);
        }
        if loose {
            return reject("invalid nested inductive datatype, nested occurrence parameters cannot contain local variables");
        }
        let ias = tc.store.mk_app_n(head, &args[..inp]);
        if let Some(&(_, aux)) = self.aux_keys.iter().find(|(k, _)| *k == ias) {
            let h = tc.store.mk_const(aux, self.levels);
            let h = tc.store.mk_app_n(h, &self.params);
            return Ok(Some(tc.store.mk_app_n(h, &args[inp..])));
        }
        let all = iv.all.clone();
        let mut result = None;
        for j_name in all {
            let Some(jiv) = tc.induct_info(j_name) else {
                return reject("nested inductive type is not declared before the block");
            };
            let jctors = jiv.ctors.clone();
            let jas = {
                let h = tc.store.mk_const(j_name, i_lvls);
                tc.store.mk_app_n(h, &args[..inp])
            };
            let aux = self.fake();
            self.names.insert(aux);
            self.aux_keys.push((jas, aux));
            self.restore.insert(aux, Restore::Ind(jas));
            // Type of the auxiliary type: the type of `J` at the arguments `Ds`.
            let jci = tc.const_info(j_name)?;
            let jty = self.inst_const_type(tc, jci, i_lvls)?;
            let (aux_ty, _) = strip_params_pi(tc, jty, inp)?;
            let aux_ty = tc.store.instantiate(aux_ty, &args[..inp]);
            let mut cts = Vec::new();
            for jc in jctors {
                let cci = tc.const_info(jc)?;
                if !matches!(cci.kind, ConstKind::Ctor(_)) {
                    return reject("nested inductive constructor list is not a constructor");
                }
                let cty = self.inst_const_type(tc, cci, i_lvls)?;
                let (pre, nfields) = strip_params_pi(tc, cty, inp)?;
                let pre = tc.store.instantiate(pre, &args[..inp]);
                let fake_c = self.fake();
                self.restore.insert(fake_c, Restore::Ctor(jas, jc));
                cts.push(CtorD { name: fake_c, real: jc, pre, res: pre, nfields, full: None });
            }
            self.tys.push(TyD { name: aux, ty: aux_ty, nidx: 0, ctors: cts });
            if j_name == i_name {
                let h = tc.store.mk_const(aux, self.levels);
                let h = tc.store.mk_app_n(h, &self.params);
                result = Some(tc.store.mk_app_n(h, &args[inp..]));
            }
        }
        match result {
            Some(r) => Ok(Some(r)),
            None => reject("nested occurrence is not in the mutual group of its inductive type"),
        }
    }

    /// The type of constant `ci` with its universe parameters set to `lv`, with the first
    /// `args.len()` binders stripped (syntactically) and instantiated with `args`. Used for the
    /// types of nested occurrences.
    fn inst_const_type(&self, tc: &mut Checker, ci: &crate::env::ConstInfo, lv: LevelsId) -> R<TermId> {
        if tc.store.levels(lv).len() != ci.level_params.len() {
            return reject("nested occurrence has the wrong number of universe levels");
        }
        let t = tc.import_expr(ci.ty);
        if ci.level_params.is_empty() {
            Ok(t)
        } else {
            Ok(tc.store.subst_params(t, &ci.level_params, lv))
        }
    }

    /// `replace_all_nested` of the reference, applied to a residual (closed over locals).
    fn replace_nested(&mut self, tc: &mut Checker, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> R<TermId> {
        if let Some(&r) = memo.get(&t) {
            return Ok(r);
        }
        let r = match self.replace_if_nested(tc, t)? {
            Some(x) => x,
            None => match tc.store.get(t) {
                Term::App(f, a) => {
                    let f2 = self.replace_nested(tc, f, memo)?;
                    let a2 = self.replace_nested(tc, a, memo)?;
                    tc.store.mk_app(f2, a2)
                }
                Term::Pi(d, b) => {
                    let d2 = self.replace_nested(tc, d, memo)?;
                    let b2 = self.replace_nested(tc, b, memo)?;
                    tc.store.mk_pi(d2, b2)
                }
                Term::Lam(d, b) => {
                    let d2 = self.replace_nested(tc, d, memo)?;
                    let b2 = self.replace_nested(tc, b, memo)?;
                    tc.store.mk_lam(d2, b2)
                }
                Term::Let(a, b, c) => {
                    let a2 = self.replace_nested(tc, a, memo)?;
                    let b2 = self.replace_nested(tc, b, memo)?;
                    let c2 = self.replace_nested(tc, c, memo)?;
                    tc.store.mk_let(a2, b2, c2)
                }
                Term::Proj(s, i, e) => {
                    let e2 = self.replace_nested(tc, e, memo)?;
                    tc.store.mk_proj(s, i, e2)
                }
                _ => t,
            },
        };
        memo.insert(t, r);
        Ok(r)
    }
}

/// Strips `n` syntactic Pi binders (no instantiation); returns the body and count of remaining Pis.
fn strip_params_pi(tc: &mut Checker, t: TermId, n: usize) -> R<(TermId, usize)> {
    let mut cur = t;
    for _ in 0..n {
        match tc.store.get(cur) {
            Term::Pi(_, b) => cur = b,
            _ => return reject("nested occurrence: fewer parameters than the inductive type declares"),
        }
    }
    Ok((cur, count_pis(tc, cur)))
}

/// Uniformity of block occurrences (`check_uniform_ind_occs`): every occurrence of a block type
/// in a constructor type is applied to exactly the parameters and the block's universe levels.
fn check_uniform(tc: &Checker, blk: &Blk, t: TermId, off: u32) -> R<()> {
    let (head, args) = spine(tc, t);
    if let Term::Const(n, ls) = tc.store.get(head) {
        if blk.orig_names.contains(&n) {
            if args.len() > blk.np {
                // over-applied: the arguments are checked below
            } else {
                let mut ok = args.len() == blk.np && off as usize >= blk.np && ls == blk.levels;
                if ok {
                    for (i, &a) in args.iter().enumerate() {
                        let want = off as u64 - 1 - i as u64;
                        match tc.store.get(a) {
                            Term::BVar(j) if j as u64 == want => {}
                            _ => {
                                ok = false;
                                break;
                            }
                        }
                    }
                }
                if !ok {
                    return reject("invalid occurrence of a datatype being declared: it must be applied to the parameters and universe levels of the declaration");
                }
                return Ok(());
            }
        }
    }
    match tc.store.get(t) {
        Term::App(f, a) => {
            check_uniform(tc, blk, f, off)?;
            check_uniform(tc, blk, a, off)
        }
        Term::Pi(d, b) | Term::Lam(d, b) => {
            check_uniform(tc, blk, d, off)?;
            check_uniform(tc, blk, b, off + 1)
        }
        Term::Let(a, b, c) => {
            check_uniform(tc, blk, a, off)?;
            check_uniform(tc, blk, b, off)?;
            check_uniform(tc, blk, c, off + 1)
        }
        Term::Proj(_, _, e) => check_uniform(tc, blk, e, off),
        _ => Ok(()),
    }
}

/// Does `t` mention an auxiliary-namespace constant (`_nested` prefix) or projection?
fn mentions_reserved(tc: &Checker, t: TermId, reserved: NameId) -> bool {
    let mut stack = vec![t];
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        match tc.store.get(x) {
            Term::Const(n, _) => {
                if name_has_prefix(tc, n, reserved) {
                    return true;
                }
            }
            Term::Proj(s, _, e) => {
                if name_has_prefix(tc, s, reserved) {
                    return true;
                }
                stack.push(e);
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
            _ => {}
        }
    }
    false
}

fn check_block(tc: &mut Checker, pos: u32, types: &[NameId], ctors: &[NameId], recs: &[NameId]) -> R<()> {
    let env = tc.env;
    if types.is_empty() {
        return reject("inductive block without types");
    }
    if has_dup(types) || has_dup(ctors) || has_dup(recs) {
        return reject("duplicate name in an inductive block");
    }
    for &n in types.iter().chain(ctors).chain(recs) {
        match env.get(n) {
            Some(ci) if ci.pos == pos => {}
            _ => return reject("inductive block member is not declared by this block"),
        }
    }

    // The types: flags, parameters and universe parameters must agree.
    let Some(ci0) = env.get(types[0]) else { return reject("missing inductive type") };
    let ConstKind::Induct(iv0) = &ci0.kind else { return reject("block type is not an inductive") };
    let lparams = ci0.level_params.clone();
    let np = iv0.num_params as usize;
    let unsafe_flag = ci0.is_unsafe;
    for &t in types {
        let Some(ci) = env.get(t) else { return reject("missing inductive type") };
        let ConstKind::Induct(iv) = &ci.kind else { return reject("block type is not an inductive") };
        if ci.level_params != lparams || iv.num_params as usize != np || ci.is_unsafe != unsafe_flag {
            return reject("inductive types of a block disagree on universe parameters, parameters or safety");
        }
        if iv.is_unsafe != unsafe_flag || iv.all.as_slice() != types {
            return reject("inductive type data does not match its block");
        }
    }
    if unsafe_flag {
        // Unsafe blocks are invisible to safe declarations. Only their flags are checked.
        for &n in ctors.iter().chain(recs) {
            match env.get(n) {
                Some(ci) if ci.is_unsafe => {}
                _ => return reject("unsafe inductive block member is marked safe"),
            }
        }
        return Ok(());
    }
    check_safe_block(tc, pos, types, ctors, recs, lparams, np)
}

fn check_safe_block(tc: &mut Checker, pos: u32, types: &[NameId], ctors: &[NameId], recs: &[NameId], lparams: Vec<NameId>, np: usize) -> R<()> {
    let env = tc.env;
    let n = types.len();

    for (i, p) in lparams.iter().enumerate() {
        if lparams[..i].contains(p) {
            return reject("duplicate universe parameter");
        }
    }
    let lvl_ids: Vec<LevelId> = lparams.iter().map(|&p| tc.store.mk_param(p)).collect();
    let levels = tc.store.mk_levels(&lvl_ids);

    // Constructor lists of the file's types, and their constructor infos.
    let mut orig_ctor_names = Vec::with_capacity(n);
    for &t in types {
        let Some(ci) = env.get(t) else { return reject("missing inductive type") };
        let ConstKind::Induct(iv) = &ci.kind else { return reject("block type is not an inductive") };
        orig_ctor_names.push(iv.ctors.clone());
    }
    let concat: Vec<NameId> = orig_ctor_names.iter().flatten().copied().collect();
    if concat.len() != ctors.len() || concat.iter().any(|c| !ctors.contains(c)) {
        return reject("constructors of the block do not match its types");
    }
    for (d, cs) in orig_ctor_names.iter().enumerate() {
        for &c in cs {
            let Some(ci) = env.get(c) else { return reject("missing constructor") };
            match &ci.kind {
                ConstKind::Ctor(cinfo) if cinfo.induct == types[d] && ci.pos == pos => {}
                _ => return reject("constructor does not belong to its type"),
            }
            if ci.level_params != lparams || ci.is_unsafe {
                return reject("constructor universe parameters or safety disagree with its block");
            }
        }
    }

    let mut blk = Blk {
        lvl_ids: lvl_ids.clone(),
        levels,
        np,
        orig_names: types.to_vec(),
        tys: Vec::new(),
        params: Vec::new(),
        ind_cnst: Vec::new(),
        result_level: tc.store.mk_zero(),
        next_depth: 0,
        fake_base: env.raw.names.len() as u32,
        fake_next: 0,
        names: types.iter().copied().collect(),
        aux_keys: Vec::new(),
        restore: FxHashMap::default(),
    };

    // Phase A: the types (check_inductive_types).
    for (d, &tname) in types.iter().enumerate() {
        let Some(ci) = env.get(tname) else { return reject("missing inductive type") };
        let ty = tc.import_expr(ci.ty);
        if tc.store.lbr(ty) > 0 {
            return reject("loose bound variable in inductive type");
        }
        tc.check_levels_declared(ty, &lparams)?;
        tc.infer(ty, true)?;
        let mut t = tc.whnf(ty)?;
        for i in 0..np {
            let Term::Pi(dom, body) = tc.store.get(t) else {
                return reject("number of parameters mismatch in inductive datatype declaration");
            };
            if d == 0 {
                let x = blk.fresh(tc, dom);
                blk.params.push(x);
            } else {
                let pty = local_type(tc, blk.params[i]);
                if !tc.is_def_eq(dom, pty)? {
                    return reject("parameters of all inductive datatypes must match");
                }
            }
            let x = blk.params[i];
            t = tc.store.instantiate(body, &[x]);
            t = tc.whnf(t)?;
        }
        let res_ty = t;
        let mut nidx = 0usize;
        loop {
            let Term::Pi(dom, body) = tc.store.get(t) else { break };
            let x = blk.fresh(tc, dom);
            t = tc.store.instantiate(body, &[x]);
            t = tc.whnf(t)?;
            nidx += 1;
        }
        let s = tc.ensure_sort(t)?;
        if d == 0 {
            blk.result_level = s;

        } else if !tc.store.level_eq(s, blk.result_level) {
            return reject("mutually inductive types must live in the same universe");
        }
        blk.tys.push(TyD { name: tname, ty: res_ty, nidx, ctors: Vec::new() });
    }
    blk.ind_cnst = types.iter().map(|&t| tc.store.mk_const(t, levels)).collect();

    // Constructors of the original types: parameters, full type, residual.
    for (d, cs) in orig_ctor_names.iter().enumerate() {
        for &c in cs {
            let Some(ci) = env.get(c) else { return reject("missing constructor") };
            let full = tc.import_expr(ci.ty);
            if tc.store.lbr(full) > 0 {
                return reject("loose bound variable in constructor type");
            }
            tc.check_levels_declared(full, &lparams)?;
            let (pre, nfields) = strip_params(tc, full, &blk.params)?;
            blk.tys[d].ctors.push(CtorD { name: c, real: c, pre, res: pre, nfields, full: Some(full) });
        }
    }

    // Phase B: the nested elimination (elim_nested_inductive_fn), on the original constructors.
    let nested_id = env.raw.find_name(&["_nested"]);
    if let Some(nid) = nested_id {
        for &t in types {
            let Some(ci) = env.get(t) else { return reject("missing inductive type") };
            let ty = tc.import_expr(ci.ty);
            if mentions_reserved(tc, ty, nid) {
                return reject("declaration uses the reserved prefix of auxiliary declarations");
            }
        }
    }
    for d in 0..n {
        for c in &blk.tys[d].ctors {
            if let (Some(full), Some(nid)) = (c.full, nested_id) {
                if mentions_reserved(tc, full, nid) {
                    return reject("declaration uses the reserved prefix of auxiliary declarations");
                }
            }
        }
    }
    for d in 0..n {
        for c in &blk.tys[d].ctors {
            if let Some(full) = c.full {
                check_uniform(tc, &blk, full, 0)?;
            }
        }
    }
    let mut q = 0usize;
    while q < blk.tys.len() {
        let nc = blk.tys[q].ctors.len();
        for c in 0..nc {
            let r = blk.tys[q].ctors[c].res;
            let mut memo = FxHashMap::default();
            let nr = blk.replace_nested(tc, r, &mut memo)?;
            blk.tys[q].ctors[c].res = nr;
        }
        q += 1;
    }
    let nnested = blk.tys.len() - n;
    // Indices of the auxiliary types.
    for d in n..blk.tys.len() {
        let mut t = blk.tys[d].ty;
        let mut k = 0usize;
        loop {
            let Term::Pi(dom, body) = tc.store.get(t) else { break };
            let x = blk.fresh(tc, dom);
            t = tc.store.instantiate(body, &[x]);
            k += 1;
        }
        blk.tys[d].nidx = k;
    }
    let ntys = blk.tys.len();
    // Block names are complete now.
    blk.ind_cnst = (0..ntys)
        .map(|d| {
            let nm = blk.tys[d].name;
            tc.store.mk_const(nm, levels)
        })
        .collect();

    // Phase C: constructors (check_constructors), on the original and on the structural view.
    for d in 0..ntys {
        let nc = blk.tys[d].ctors.len();
        for c in 0..nc {
            let (pre, res, full) = {
                let cd = &blk.tys[d].ctors[c];
                (cd.pre, cd.res, cd.full)
            };
            let closed = match full {
                Some(f) => f,
                None => close_params(tc, &blk, pre)?,
            };
            tc.infer(closed, true)?;
            if let Some(f) = full {
                // Parameters of the constructor agree with the block's parameters.
                let mut t = f;
                for i in 0..np {
                    let Term::Pi(dom, body) = tc.store.get(t) else {
                        return reject("constructor has fewer parameters than the block");
                    };
                    let pty = local_type(tc, blk.params[i]);
                    if !tc.is_def_eq(dom, pty)? {
                        return reject("constructor parameters do not match the inductive datatype parameters");
                    }
                    t = tc.store.instantiate(body, &[blk.params[i]]);
                }
            }
            let (fields, _) = blk.typed_fields(tc, pre)?;
            for (_, l) in fields {
                let ok = tc.store.level_leq(l, blk.result_level) || tc.store.level_is_zero(blk.result_level);
                if !ok {
                    return reject("universe level of a constructor field is too big for its inductive datatype");
                }
            }
            // Positivity on the structural view.
            let mut t = res;
            while let Term::Pi(dom, body) = tc.store.get(t) {
                blk.check_positivity(tc, dom)?;
                let x = blk.fresh(tc, dom);
                t = tc.store.instantiate(body, &[x]);
            }
            if !blk.is_valid_ind_app(tc, t, d) {
                return reject("invalid return type of a constructor");
            }
        }
    }

    // Phase D: flags.
    let mut is_rec = false;
    for d in 0..ntys {
        for c in &blk.tys[d].ctors {
            let mut t = c.res;
            while let Term::Pi(dom, body) = tc.store.get(t) {
                if blk.has_ind_occ(tc, dom) {
                    is_rec = true;
                }
                t = body;
            }
        }
    }
    let mut is_reflexive = false;
    for d in 0..ntys {
        for c in 0..blk.tys[d].ctors.len() {
            let mut t = blk.tys[d].ctors[c].res;
            while let Term::Pi(dom, body) = tc.store.get(t) {
                if matches!(tc.store.get(dom), Term::Pi(..)) && blk.has_ind_occ(tc, dom) {
                    is_reflexive = true;
                }
                let x = blk.fresh(tc, dom);
                t = tc.store.instantiate(body, &[x]);
            }
        }
    }

    // Phase E: elimination level and K (init_elim_level, init_K_target).
    let elim_zero = if tc.store.level_never_zero(blk.result_level) {
        false
    } else if ntys > 1 {
        true
    } else {
        match blk.tys[0].ctors.len() {
            0 => false,
            1 => {
                let pre = blk.tys[0].ctors[0].pre;
                let (fields, fin) = blk.typed_fields(tc, pre)?;
                let (_, args) = spine(tc, fin);
                let mut zero = false;
                for (x, l) in fields {
                    if !tc.store.level_is_zero(l) && !args.contains(&x) {
                        zero = true;
                        break;
                    }
                }
                zero
            }
            _ => true,
        }
    };
    let (elim_level, elim_name) = if elim_zero {
        (tc.store.mk_zero(), None)
    } else {
        let mut cand = String::from("u");
        let mut k = 1;
        loop {
            match env.raw.find_name(&[cand.as_str()]) {
                Some(id) if lparams.contains(&id) => {
                    cand = format!("u_{k}");
                    k += 1;
                }
                _ => break,
            }
        }
        let Some(id) = env.raw.find_name(&[cand.as_str()]) else {
            return reject("missing elimination universe name");
        };
        (tc.store.mk_param(id), Some(id))
    };
    let k_target = ntys == 1 && tc.store.level_is_zero(blk.result_level) && blk.tys[0].ctors.len() == 1 && count_pis(tc, blk.tys[0].ctors[0].pre) == 0;

    // Recursor names: the real ones (found among the declared recursors) and the ids used in terms.
    let mut rec_real = Vec::with_capacity(ntys);
    for d in 0..ntys {
        let found = if d < n {
            find_rec(tc, recs, types[d], "rec")
        } else {
            find_rec(tc, recs, types[0], &format!("rec_{}", d - n + 1))
        };
        let Some(r) = found else { return reject("inductive block is missing a recursor the declaration implies") };
        rec_real.push(r);
    }
    if recs.len() != ntys {
        return reject("inductive block declares a recursor it does not produce");
    }
    let mut rec_id = Vec::with_capacity(ntys);
    for d in 0..ntys {
        if d < n {
            rec_id.push(rec_real[d]);
        } else {
            let f = blk.fake();
            blk.restore.insert(f, Restore::Rec(rec_real[d]));
            rec_id.push(f);
        }
    }
    let rec_levels = match elim_name {
        Some(_) => {
            let mut v = vec![elim_level];
            v.extend_from_slice(&blk.lvl_ids);
            tc.store.mk_levels(&v)
        }
        None => levels,
    };
    let rec_lparams: Vec<NameId> = match elim_name {
        Some(id) => {
            let mut v = vec![id];
            v.extend_from_slice(&lparams);
            v
        }
        None => lparams.clone(),
    };

    // Phase F: recursor locals (mk_rec_infos).
    let elim_sort = tc.store.mk_sort(elim_level);
    let mut infos: Vec<IndRec> = Vec::with_capacity(ntys);
    for d in 0..ntys {
        let mut t = blk.tys[d].ty;
        let mut indices = Vec::new();
        loop {
            t = tc.whnf(t)?;
            let Term::Pi(dom, body) = tc.store.get(t) else { break };
            let x = blk.fresh(tc, dom);
            indices.push(x);
            t = tc.store.instantiate(body, &[x]);
        }
        let mut app_args = blk.params.clone();
        app_args.extend_from_slice(&indices);
        let ind_app = tc.store.mk_app_n(blk.ind_cnst[d], &app_args);
        let major = blk.fresh(tc, ind_app);
        let mut motive_xs = indices.clone();
        motive_xs.push(major);
        let c_ty = blk.close(tc, &motive_xs, elim_sort, true)?;
        let c = blk.fresh(tc, c_ty);
        infos.push(IndRec { c, indices, major });
    }
    let cs: Vec<TermId> = infos.iter().map(|i| i.c).collect();
    let mut minors: Vec<TermId> = Vec::new();
    let mut ctor_recs: Vec<Vec<CtorRec>> = Vec::with_capacity(ntys);
    for d in 0..ntys {
        let mut per = Vec::new();
        let nc = blk.tys[d].ctors.len();
        for c in 0..nc {
            let (cname, res) = {
                let cd = &blk.tys[d].ctors[c];
                (cd.name, cd.res)
            };
            let mut t = res;
            let mut b_u = Vec::new();
            let mut u = Vec::new();
            while let Term::Pi(dom, body) = tc.store.get(t) {
                let x = blk.fresh(tc, dom);
                b_u.push(x);
                if blk.is_rec_argument(tc, dom)?.is_some() {
                    u.push(x);
                }
                t = tc.store.instantiate(body, &[x]);
            }
            let (it_idx, it_indices) = blk.i_indices(tc, t)?;
            let inner = tc.store.mk_app_n(infos[it_idx].c, &it_indices);
            let mut intro_args = blk.params.clone();
            intro_args.extend_from_slice(&b_u);
            let intro_c = tc.store.mk_const(cname, levels);
            let intro = tc.store.mk_app_n(intro_c, &intro_args);
            let c_app = tc.store.mk_app(inner, intro);
            let mut us = Vec::new();
            let mut vs = Vec::new();
            for &ui in &u {
                let ty0 = tc.infer(ui, false)?;
                let mut uty = tc.whnf(ty0)?;
                let mut xs = Vec::new();
                while let Term::Pi(dom, body) = tc.store.get(uty) {
                    let y = blk.fresh(tc, dom);
                    xs.push(y);
                    let b2 = tc.store.instantiate(body, &[y]);
                    uty = tc.whnf(b2)?;
                }
                let (it_idx2, it_indices2) = blk.i_indices(tc, uty)?;
                let inner2 = tc.store.mk_app_n(infos[it_idx2].c, &it_indices2);
                let ui_app = tc.store.mk_app_n(ui, &xs);
                let capp2 = tc.store.mk_app(inner2, ui_app);
                let v_ty = blk.close(tc, &xs, capp2, true)?;
                let v = blk.fresh(tc, v_ty);
                vs.push(v);
                us.push(UData { u: ui, xs, it_idx: it_idx2, it_indices: it_indices2 });
            }
            let mut minor_xs = b_u.clone();
            minor_xs.extend_from_slice(&vs);
            let minor_ty = blk.close(tc, &minor_xs, c_app, true)?;
            let minor = blk.fresh(tc, minor_ty);
            minors.push(minor);
            per.push(CtorRec { b_u, us, minor });
        }
        ctor_recs.push(per);
    }

    // Phase G: recursor types and rules (mk_rec_rules, declare_recursors).
    let nminors = minors.len();
    let mut derived: Vec<DerivedRec> = Vec::with_capacity(ntys);
    for d in 0..ntys {
        let info = &infos[d];
        let c_app0 = tc.store.mk_app_n(info.c, &info.indices);
        let c_app = tc.store.mk_app(c_app0, info.major);
        let mut all_xs = blk.params.clone();
        all_xs.extend_from_slice(&cs);
        all_xs.extend_from_slice(&minors);
        all_xs.extend_from_slice(&info.indices);
        all_xs.push(info.major);
        let rec_ty = blk.close(tc, &all_xs, c_app, true)?;
        let mut rules = Vec::new();
        for (ci, cr) in ctor_recs[d].iter().enumerate() {
            let mut vs = Vec::new();
            for ud in &cr.us {
                let rc = tc.store.mk_const(rec_id[ud.it_idx], rec_levels);
                let mut args = blk.params.clone();
                args.extend_from_slice(&cs);
                args.extend_from_slice(&minors);
                args.extend_from_slice(&ud.it_indices);
                let ua = tc.store.mk_app_n(ud.u, &ud.xs);
                args.push(ua);
                let rec_app = tc.store.mk_app_n(rc, &args);
                vs.push(blk.close(tc, &ud.xs, rec_app, false)?);
            }
            let minor_app = tc.store.mk_app_n(cr.minor, &cr.b_u);
            let e_app = tc.store.mk_app_n(minor_app, &vs);
            let mut lam_xs = blk.params.clone();
            lam_xs.extend_from_slice(&cs);
            lam_xs.extend_from_slice(&minors);
            lam_xs.extend_from_slice(&cr.b_u);
            let rhs = blk.close(tc, &lam_xs, e_app, false)?;
            let ctor_real = blk.tys[d].ctors[ci].real;
            rules.push((ctor_real, cr.b_u.len(), rhs));
        }
        let lparams_d = rec_lparams.clone();
        derived.push(DerivedRec { lparams: lparams_d, ty: rec_ty, nidx: blk.tys[d].nidx, rules });
    }

    // Phase H: compare with the file (I1). Inductive types.
    let all_real: Vec<NameId> = types.to_vec();
    for d in 0..n {
        let Some(ci) = env.get(types[d]) else { return reject("missing inductive type") };
        let ConstKind::Induct(iv) = &ci.kind else { return reject("block type is not an inductive") };
        if iv.num_params as usize != np {
            return reject("numParams mismatch");
        }
        if iv.num_indices as usize != blk.tys[d].nidx {
            return reject("numIndices mismatch");
        }
        if iv.all != all_real {
            return reject("all mismatch");
        }
        if iv.ctors != orig_ctor_names[d] {
            return reject("constructor list mismatch");
        }
        if iv.num_nested as usize != nnested {
            return reject("numNested mismatch");
        }
        if iv.is_rec != is_rec {
            return reject("isRec mismatch");
        }
        if iv.is_reflexive != is_reflexive {
            return reject("isReflexive mismatch");
        }
        if iv.is_unsafe {
            return reject("safety mismatch");
        }
    }
    // Constructors.
    for d in 0..n {
        for (j, &c) in orig_ctor_names[d].iter().enumerate() {
            let Some(ci) = env.get(c) else { return reject("missing constructor") };
            let ConstKind::Ctor(cinfo) = &ci.kind else { return reject("constructor kind mismatch") };
            let nfields = blk.tys[d].ctors[j].nfields;
            if cinfo.induct != types[d] || cinfo.cidx as usize != j || cinfo.num_params as usize != np || cinfo.num_fields as usize != nfields || ci.is_unsafe {
                return reject("constructor data mismatch");
            }
        }
    }
    // Recursors.
    let total_ctors: usize = blk.tys.iter().map(|t| t.ctors.len()).sum();
    if total_ctors != nminors {
        return reject("internal: minor premise count");
    }
    for d in 0..ntys {
        let rname = rec_real[d];
        let Some(rci) = env.get(rname) else { return reject("missing recursor") };
        let ConstKind::Rec(ri) = &rci.kind else { return reject("recursor kind mismatch") };
        let der = &derived[d];
        if rci.level_params != der.lparams {
            return reject("recursor universe parameters mismatch");
        }
        // The derived type is well typed (defensive, as the reference's check_recursors).
        tc.infer(der.ty, true)?;
        let fty = tc.import_expr(rci.ty);
        if fty != der.ty && !tc.is_def_eq(fty, der.ty)? {
            return reject(format!("recursor type mismatch for '{}'", env.raw.name_to_string(rname)));
        }
        if ri.all != all_real {
            return reject("recursor all mismatch");
        }
        if ri.num_params as usize != np || ri.num_indices as usize != der.nidx || ri.num_motives as usize != ntys || ri.num_minors as usize != nminors {
            return reject("recursor counts mismatch");
        }
        if ri.k != k_target {
            return reject("recursor k flag mismatch");
        }
        if ri.is_unsafe || rci.is_unsafe {
            return reject("recursor safety mismatch");
        }
        if ri.rules.len() != der.rules.len() {
            return reject("recursor rule count mismatch");
        }
        for (rule, (dc, dn, drhs)) in ri.rules.iter().zip(der.rules.iter()) {
            if rule.ctor != *dc || rule.nfields as usize != *dn {
                return reject("recursor rule header mismatch");
            }
            let frhs = tc.import_expr(rule.rhs);
            if frhs != *drhs && !tc.is_def_eq(frhs, *drhs)? {
                return reject("recursor rule right-hand side mismatch");
            }
        }
    }
    Ok(())
}

/// Closes the residual `pre` (over the parameter locals) under the parameter binders, giving a
/// closed type that can be checked. Used for auxiliary constructor types, which have no own type.
fn close_params(tc: &mut Checker, blk: &Blk, pre: TermId) -> R<TermId> {
    blk.close(tc, &blk.params, pre, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    /// Mutual `Prop` block `A.mk : B -> A`, `B.mk : A -> B` (no parameters, no universe
    /// parameters) with the recursors written out from the Lean 4 rules: `A.rec` and `B.rec`
    /// take two motives and two minor premises, and each rule has one field.
    const MUTUAL: &str = r#"{"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "x", "version": "4.34.1"}}}
{"sort":0,"ie":0}
{"in":1,"str":{"pre":0,"str":"B"}}
{"const":{"name":1,"us":[]},"ie":1}
{"in":2,"str":{"pre":0,"str":"A"}}
{"const":{"name":2,"us":[]},"ie":2}
{"in":3,"str":{"pre":0,"str":"a"}}
{"forallE":{"binderInfo":"default","body":2,"name":3,"type":1},"ie":3}
{"const":{"name":2,"us":[]},"ie":4}
{"const":{"name":1,"us":[]},"ie":5}
{"forallE":{"binderInfo":"default","body":5,"name":3,"type":4},"ie":6}
{"sort":0,"ie":7}
{"const":{"name":2,"us":[]},"ie":8}
{"sort":0,"ie":9}
{"in":4,"str":{"pre":0,"str":"x"}}
{"forallE":{"binderInfo":"default","body":9,"name":4,"type":8},"ie":10}
{"const":{"name":1,"us":[]},"ie":11}
{"sort":0,"ie":12}
{"forallE":{"binderInfo":"default","body":12,"name":4,"type":11},"ie":13}
{"const":{"name":1,"us":[]},"ie":14}
{"bvar":1,"ie":15}
{"bvar":0,"ie":16}
{"app":{"arg":16,"fn":15},"ie":17}
{"bvar":3,"ie":18}
{"in":5,"str":{"pre":2,"str":"mk"}}
{"const":{"name":5,"us":[]},"ie":19}
{"bvar":1,"ie":20}
{"app":{"arg":20,"fn":19},"ie":21}
{"app":{"arg":21,"fn":18},"ie":22}
{"in":6,"str":{"pre":0,"str":"ih"}}
{"forallE":{"binderInfo":"default","body":22,"name":6,"type":17},"ie":23}
{"forallE":{"binderInfo":"default","body":23,"name":3,"type":14},"ie":24}
{"const":{"name":2,"us":[]},"ie":25}
{"bvar":3,"ie":26}
{"bvar":0,"ie":27}
{"app":{"arg":27,"fn":26},"ie":28}
{"bvar":3,"ie":29}
{"in":7,"str":{"pre":1,"str":"mk"}}
{"const":{"name":7,"us":[]},"ie":30}
{"bvar":1,"ie":31}
{"app":{"arg":31,"fn":30},"ie":32}
{"app":{"arg":32,"fn":29},"ie":33}
{"forallE":{"binderInfo":"default","body":33,"name":6,"type":28},"ie":34}
{"forallE":{"binderInfo":"default","body":34,"name":3,"type":25},"ie":35}
{"const":{"name":2,"us":[]},"ie":36}
{"bvar":4,"ie":37}
{"bvar":0,"ie":38}
{"app":{"arg":38,"fn":37},"ie":39}
{"in":8,"str":{"pre":0,"str":"t"}}
{"forallE":{"binderInfo":"default","body":39,"name":8,"type":36},"ie":40}
{"in":9,"str":{"pre":0,"str":"mB"}}
{"forallE":{"binderInfo":"default","body":40,"name":9,"type":35},"ie":41}
{"in":10,"str":{"pre":0,"str":"mA"}}
{"forallE":{"binderInfo":"default","body":41,"name":10,"type":24},"ie":42}
{"in":11,"str":{"pre":0,"str":"m2"}}
{"forallE":{"binderInfo":"default","body":42,"name":11,"type":13},"ie":43}
{"in":12,"str":{"pre":0,"str":"m1"}}
{"forallE":{"binderInfo":"default","body":43,"name":12,"type":10},"ie":44}
{"const":{"name":2,"us":[]},"ie":45}
{"sort":0,"ie":46}
{"forallE":{"binderInfo":"default","body":46,"name":4,"type":45},"ie":47}
{"const":{"name":1,"us":[]},"ie":48}
{"sort":0,"ie":49}
{"forallE":{"binderInfo":"default","body":49,"name":4,"type":48},"ie":50}
{"const":{"name":1,"us":[]},"ie":51}
{"bvar":1,"ie":52}
{"bvar":0,"ie":53}
{"app":{"arg":53,"fn":52},"ie":54}
{"bvar":3,"ie":55}
{"const":{"name":5,"us":[]},"ie":56}
{"bvar":1,"ie":57}
{"app":{"arg":57,"fn":56},"ie":58}
{"app":{"arg":58,"fn":55},"ie":59}
{"forallE":{"binderInfo":"default","body":59,"name":6,"type":54},"ie":60}
{"forallE":{"binderInfo":"default","body":60,"name":3,"type":51},"ie":61}
{"const":{"name":2,"us":[]},"ie":62}
{"bvar":3,"ie":63}
{"bvar":0,"ie":64}
{"app":{"arg":64,"fn":63},"ie":65}
{"bvar":3,"ie":66}
{"const":{"name":7,"us":[]},"ie":67}
{"bvar":1,"ie":68}
{"app":{"arg":68,"fn":67},"ie":69}
{"app":{"arg":69,"fn":66},"ie":70}
{"forallE":{"binderInfo":"default","body":70,"name":6,"type":65},"ie":71}
{"forallE":{"binderInfo":"default","body":71,"name":3,"type":62},"ie":72}
{"const":{"name":1,"us":[]},"ie":73}
{"bvar":3,"ie":74}
{"bvar":0,"ie":75}
{"app":{"arg":75,"fn":74},"ie":76}
{"forallE":{"binderInfo":"default","body":76,"name":8,"type":73},"ie":77}
{"forallE":{"binderInfo":"default","body":77,"name":9,"type":72},"ie":78}
{"forallE":{"binderInfo":"default","body":78,"name":10,"type":61},"ie":79}
{"forallE":{"binderInfo":"default","body":79,"name":11,"type":50},"ie":80}
{"forallE":{"binderInfo":"default","body":80,"name":12,"type":47},"ie":81}
{"const":{"name":2,"us":[]},"ie":82}
{"sort":0,"ie":83}
{"forallE":{"binderInfo":"default","body":83,"name":4,"type":82},"ie":84}
{"const":{"name":1,"us":[]},"ie":85}
{"sort":0,"ie":86}
{"forallE":{"binderInfo":"default","body":86,"name":4,"type":85},"ie":87}
{"const":{"name":1,"us":[]},"ie":88}
{"bvar":1,"ie":89}
{"bvar":0,"ie":90}
{"app":{"arg":90,"fn":89},"ie":91}
{"bvar":3,"ie":92}
{"const":{"name":5,"us":[]},"ie":93}
{"bvar":1,"ie":94}
{"app":{"arg":94,"fn":93},"ie":95}
{"app":{"arg":95,"fn":92},"ie":96}
{"forallE":{"binderInfo":"default","body":96,"name":6,"type":91},"ie":97}
{"forallE":{"binderInfo":"default","body":97,"name":3,"type":88},"ie":98}
{"const":{"name":2,"us":[]},"ie":99}
{"bvar":3,"ie":100}
{"bvar":0,"ie":101}
{"app":{"arg":101,"fn":100},"ie":102}
{"bvar":3,"ie":103}
{"const":{"name":7,"us":[]},"ie":104}
{"bvar":1,"ie":105}
{"app":{"arg":105,"fn":104},"ie":106}
{"app":{"arg":106,"fn":103},"ie":107}
{"forallE":{"binderInfo":"default","body":107,"name":6,"type":102},"ie":108}
{"forallE":{"binderInfo":"default","body":108,"name":3,"type":99},"ie":109}
{"const":{"name":1,"us":[]},"ie":110}
{"bvar":2,"ie":111}
{"bvar":0,"ie":112}
{"app":{"arg":112,"fn":111},"ie":113}
{"in":13,"str":{"pre":1,"str":"rec"}}
{"const":{"name":13,"us":[]},"ie":114}
{"bvar":4,"ie":115}
{"app":{"arg":115,"fn":114},"ie":116}
{"bvar":3,"ie":117}
{"app":{"arg":117,"fn":116},"ie":118}
{"bvar":2,"ie":119}
{"app":{"arg":119,"fn":118},"ie":120}
{"bvar":1,"ie":121}
{"app":{"arg":121,"fn":120},"ie":122}
{"bvar":0,"ie":123}
{"app":{"arg":123,"fn":122},"ie":124}
{"app":{"arg":124,"fn":113},"ie":125}
{"lam":{"binderInfo":"default","body":125,"name":3,"type":110},"ie":126}
{"lam":{"binderInfo":"default","body":126,"name":9,"type":109},"ie":127}
{"lam":{"binderInfo":"default","body":127,"name":10,"type":98},"ie":128}
{"lam":{"binderInfo":"default","body":128,"name":11,"type":87},"ie":129}
{"lam":{"binderInfo":"default","body":129,"name":12,"type":84},"ie":130}
{"const":{"name":2,"us":[]},"ie":131}
{"sort":0,"ie":132}
{"forallE":{"binderInfo":"default","body":132,"name":4,"type":131},"ie":133}
{"const":{"name":1,"us":[]},"ie":134}
{"sort":0,"ie":135}
{"forallE":{"binderInfo":"default","body":135,"name":4,"type":134},"ie":136}
{"const":{"name":1,"us":[]},"ie":137}
{"bvar":1,"ie":138}
{"bvar":0,"ie":139}
{"app":{"arg":139,"fn":138},"ie":140}
{"bvar":3,"ie":141}
{"const":{"name":5,"us":[]},"ie":142}
{"bvar":1,"ie":143}
{"app":{"arg":143,"fn":142},"ie":144}
{"app":{"arg":144,"fn":141},"ie":145}
{"forallE":{"binderInfo":"default","body":145,"name":6,"type":140},"ie":146}
{"forallE":{"binderInfo":"default","body":146,"name":3,"type":137},"ie":147}
{"const":{"name":2,"us":[]},"ie":148}
{"bvar":3,"ie":149}
{"bvar":0,"ie":150}
{"app":{"arg":150,"fn":149},"ie":151}
{"bvar":3,"ie":152}
{"const":{"name":7,"us":[]},"ie":153}
{"bvar":1,"ie":154}
{"app":{"arg":154,"fn":153},"ie":155}
{"app":{"arg":155,"fn":152},"ie":156}
{"forallE":{"binderInfo":"default","body":156,"name":6,"type":151},"ie":157}
{"forallE":{"binderInfo":"default","body":157,"name":3,"type":148},"ie":158}
{"const":{"name":2,"us":[]},"ie":159}
{"bvar":1,"ie":160}
{"bvar":0,"ie":161}
{"app":{"arg":161,"fn":160},"ie":162}
{"in":14,"str":{"pre":2,"str":"rec"}}
{"const":{"name":14,"us":[]},"ie":163}
{"bvar":4,"ie":164}
{"app":{"arg":164,"fn":163},"ie":165}
{"bvar":3,"ie":166}
{"app":{"arg":166,"fn":165},"ie":167}
{"bvar":2,"ie":168}
{"app":{"arg":168,"fn":167},"ie":169}
{"bvar":1,"ie":170}
{"app":{"arg":170,"fn":169},"ie":171}
{"bvar":0,"ie":172}
{"app":{"arg":172,"fn":171},"ie":173}
{"app":{"arg":173,"fn":162},"ie":174}
{"lam":{"binderInfo":"default","body":174,"name":3,"type":159},"ie":175}
{"lam":{"binderInfo":"default","body":175,"name":9,"type":158},"ie":176}
{"lam":{"binderInfo":"default","body":176,"name":10,"type":147},"ie":177}
{"lam":{"binderInfo":"default","body":177,"name":11,"type":136},"ie":178}
{"lam":{"binderInfo":"default","body":178,"name":12,"type":133},"ie":179}
{"inductive":{"ctors":[{"cidx":0,"induct":2,"isUnsafe":false,"levelParams":[],"name":5,"numFields":1,"numParams":0,"type":3},{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":7,"numFields":1,"numParams":0,"type":6}],"recs":[{"all":[2,1],"isUnsafe":false,"k":false,"levelParams":[],"name":14,"numIndices":0,"numMinors":2,"numMotives":2,"numParams":0,"rules":[{"ctor":5,"nfields":1,"rhs":130}],"type":44},{"all":[2,1],"isUnsafe":false,"k":false,"levelParams":[],"name":13,"numIndices":0,"numMinors":2,"numMotives":2,"numParams":0,"rules":[{"ctor":7,"nfields":1,"rhs":179}],"type":81}],"types":[{"all":[2,1],"ctors":[5],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":2,"numIndices":0,"numNested":0,"numParams":0,"type":7},{"all":[2,1],"ctors":[7],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":7}]}}
"#;

    fn check_file(src: &str) -> Result<(), String> {
        let env = parse::load(src.as_bytes()).map_err(|e| format!("{:?}", e))?;
        let mut tc = Checker::new(&env);
        for pos in 0..env.raw.decls.len() {
            tc.check_decl(pos as u32).map_err(|f| format!("{:?}", f))?;
        }
        Ok(())
    }

    #[test]
    fn mutual_block_accepted() {
        assert_eq!(check_file(MUTUAL), Ok(()));
    }

    #[test]
    fn mutual_block_rule_field_count_rejected() {
        let bad = MUTUAL.replacen("\"nfields\":1", "\"nfields\":0", 1);
        assert!(check_file(&bad).is_err());
    }

    #[test]
    fn mutual_block_minor_count_rejected() {
        let bad = MUTUAL.replacen("\"numMinors\":2", "\"numMinors\":1", 1);
        assert!(check_file(&bad).is_err());
    }

    #[test]
    fn mutual_block_is_rec_flag_rejected() {
        let bad = MUTUAL.replacen("\"isRec\":true", "\"isRec\":false", 1);
        assert!(check_file(&bad).is_err());
    }
}

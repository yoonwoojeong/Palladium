//! The four `Quot` constants (quot.cpp, environment::add_quot). Each constant's file type is
//! compared with the type the reference builds; `Eq` must have the expected shape.
//! See docs/CHECKER.md section 4.

use crate::env::{ConstKind, NameId, QuotKind};
use crate::store::{LevelId, Term, TermId};
use crate::tc::{reject, Checker, R};

/// Abstracts the locals `xs` (in order) into Pi binders over `body`.
fn mk_pis(tc: &mut Checker, xs: &[TermId], body: TermId) -> TermId {
    let mut r = tc.store.abstract_locals(body, xs);
    for i in (0..xs.len()).rev() {
        let ty = match tc.store.get(xs[i]) {
            Term::Local(l) => tc.store.local_type(l),
            _ => return r,
        };
        let dom = tc.store.abstract_locals(ty, &xs[..i]);
        r = tc.store.mk_pi(dom, r);
    }
    r
}

/// Checks `Eq : {α : Sort u} → α → α → Prop` and `Eq.refl : {α : Sort u} → (a : α) → Eq α a a`.
fn check_eq_type(tc: &mut Checker) -> R<()> {
    let Some(eq) = tc.env.builtins.eq_ty else { return reject("Eq is not declared") };
    let info = tc.const_info(eq)?;
    let ConstKind::Induct(iv) = &info.kind else { return reject("Eq is not an inductive type") };
    if info.level_params.len() != 1 || iv.ctors.len() != 1 {
        return reject("Eq has an unexpected shape");
    }
    let u = tc.store.mk_param(info.level_params[0]);
    let sort_u = tc.store.mk_sort(u);
    let zero = tc.store.mk_zero();
    let prop = tc.store.mk_sort(zero);
    let alpha = tc.store.mk_local(0, sort_u);
    let inner = tc.store.mk_pi(alpha, prop);
    let body = tc.store.mk_pi(alpha, inner);
    let expected = mk_pis(tc, &[alpha], body);
    let t = tc.import_expr(info.ty);
    if t != expected {
        return reject("Eq has an unexpected type");
    }
    let refl = iv.ctors[0];
    let rinfo = tc.const_info(refl)?;
    if rinfo.level_params.len() != 1 {
        return reject("Eq.refl has an unexpected shape");
    }
    let ur = tc.store.mk_param(rinfo.level_params[0]);
    let sort_ur = tc.store.mk_sort(ur);
    let alpha2 = tc.store.mk_local(0, sort_ur);
    let a = tc.store.mk_local(1, alpha2);
    let lv = tc.store.mk_levels(&[ur]);
    let eq_c = tc.store.mk_const(eq, lv);
    let b = tc.store.mk_app_n(eq_c, &[alpha2, a, a]);
    let expected = mk_pis(tc, &[alpha2, a], b);
    let t = tc.import_expr(rinfo.ty);
    if t != expected {
        return reject("Eq.refl has an unexpected type");
    }
    Ok(())
}

/// Names of the quotient constants and of `Eq`.
#[derive(Clone, Copy)]
struct QuotNames {
    quot: NameId,
    mk: NameId,
    eq: NameId,
}

/// The canonical type of the quotient constant `kind`. `u` is the level `Param u`, `v` the
/// level `Param v` (used only by `lift`).
fn expected_type(tc: &mut Checker, kind: QuotKind, n: QuotNames, u: LevelId, v: LevelId) -> TermId {
    let u_lvls = tc.store.mk_levels(&[u]);
    let quot_c = tc.store.mk_const(n.quot, u_lvls);
    let mk_c = tc.store.mk_const(n.mk, u_lvls);
    let sort_u = tc.store.mk_sort(u);
    let zero = tc.store.mk_zero();
    let prop = tc.store.mk_sort(zero);
    // `{α : Sort u} (r : α → α → Prop)`, used by every kind; locals at depths 0 and 1.
    let alpha = tc.store.mk_local(0, sort_u);
    let inner = tc.store.mk_pi(alpha, prop);
    let rty = tc.store.mk_pi(alpha, inner);
    let r = tc.store.mk_local(1, rty);
    let qr = {
        let t = tc.store.mk_app(quot_c, alpha);
        tc.store.mk_app(t, r)
    };
    match kind {
        QuotKind::Type => {
            // Quot : {α : Sort u} → (α → α → Prop) → Sort u
            mk_pis(tc, &[alpha, r], sort_u)
        }
        QuotKind::Ctor => {
            // Quot.mk : {α : Sort u} → {r : α → α → Prop} → (a : α) → @Quot α r
            let a = tc.store.mk_local(2, alpha);
            mk_pis(tc, &[alpha, r, a], qr)
        }
        QuotKind::Lift => {
            // Quot.lift : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
            //   → (∀ a b : α, r a b → f a = f b) → @Quot α r → β
            let v_lvls = tc.store.mk_levels(&[v]);
            let sort_v = tc.store.mk_sort(v);
            let beta = tc.store.mk_local(2, sort_v);
            let fty = tc.store.mk_pi(alpha, beta);
            let f = tc.store.mk_local(3, fty);
            let a = tc.store.mk_local(4, alpha);
            let b = tc.store.mk_local(5, alpha);
            let r_a_b = {
                let t = tc.store.mk_app(r, a);
                tc.store.mk_app(t, b)
            };
            let eq_c = tc.store.mk_const(n.eq, v_lvls);
            let fa = tc.store.mk_app(f, a);
            let fb = tc.store.mk_app(f, b);
            let eq_app = {
                let t = tc.store.mk_app(eq_c, beta);
                let t = tc.store.mk_app(t, fa);
                tc.store.mk_app(t, fb)
            };
            let imp = tc.store.mk_pi(r_a_b, eq_app);
            let sanity = mk_pis(tc, &[a, b], imp);
            let tail = tc.store.mk_pi(qr, beta);
            let body = tc.store.mk_pi(sanity, tail);
            mk_pis(tc, &[alpha, r, beta, f], body)
        }
        QuotKind::Ind => {
            // Quot.ind : {α : Sort u} → {r : α → α → Prop} → {β : @Quot α r → Prop}
            //   → (∀ a : α, β (@Quot.mk α r a)) → ∀ q : @Quot α r, β q
            let bty = tc.store.mk_pi(qr, prop);
            let beta = tc.store.mk_local(2, bty);
            let a = tc.store.mk_local(3, alpha);
            let mk_a = {
                let t = tc.store.mk_app(mk_c, alpha);
                let t = tc.store.mk_app(t, r);
                tc.store.mk_app(t, a)
            };
            let beta_mk = tc.store.mk_app(beta, mk_a);
            let all_quot = mk_pis(tc, &[a], beta_mk);
            let q = tc.store.mk_local(4, qr);
            let beta_q = tc.store.mk_app(beta, q);
            let tail = mk_pis(tc, &[q], beta_q);
            let body = tc.store.mk_pi(all_quot, tail);
            mk_pis(tc, &[alpha, r, beta], body)
        }
    }
}

/// Checks the `Quot` constant `name` declared at position `pos`.
pub fn check_quot(tc: &mut Checker, pos: u32, name: NameId) -> R<()> {
    let env = tc.env;
    let info = match env.get(name) {
        Some(i) if i.pos == pos => i,
        _ => return reject("quot declaration does not match the constant table"),
    };
    let kind = match info.kind {
        ConstKind::Quot(k) => k,
        _ => return reject("quot declaration has the wrong kind"),
    };
    let (Some(u_id), Some(v_id)) = (env.raw.find_name(&["u"]), env.raw.find_name(&["v"])) else {
        return reject("quot declaration without universe names u / v");
    };
    let (canon, want_params): (&[&str], Vec<NameId>) = match kind {
        QuotKind::Type => (&["Quot"], vec![u_id]),
        QuotKind::Ctor => (&["Quot", "mk"], vec![u_id]),
        QuotKind::Lift => (&["Quot", "lift"], vec![u_id, v_id]),
        QuotKind::Ind => (&["Quot", "ind"], vec![u_id]),
    };
    if env.raw.find_name(canon) != Some(name) {
        return reject("quot declaration has an unexpected name");
    }
    if info.level_params != want_params {
        return reject("quot declaration has unexpected universe parameters");
    }
    let (Some(quot), Some(mk)) = (env.raw.find_name(&["Quot"]), env.raw.find_name(&["Quot", "mk"])) else {
        return reject("Quot is not declared");
    };
    let Some(eq) = env.builtins.eq_ty else { return reject("Eq is not declared") };
    check_eq_type(tc)?;
    let u = tc.store.mk_param(u_id);
    let v = tc.store.mk_param(v_id);
    let expected = expected_type(tc, kind, QuotNames { quot, mk, eq }, u, v);
    let imp = tc.import_expr(info.ty);
    if imp != expected && !tc.is_def_eq(imp, expected)? {
        return reject("quot declaration has an unexpected type");
    }
    Ok(())
}

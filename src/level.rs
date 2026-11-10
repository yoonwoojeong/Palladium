//! Universe levels: smart constructors, parameter substitution, and the complete
//! `leq` / `eq` decision procedure of docs/DESIGN.md section 4. Storage is in `store.rs`.
//!
//! Semantics: a level is a function from assignments of naturals to parameters to naturals;
//! `imax a b = 0 if b = 0 else max a b`. `level_leq(a, b)` holds iff `a <= b` under every
//! assignment.

use crate::env::NameId;
use crate::store::{hash_lnode, LMeta, LNode, Level, LevelId, Store, L_IMAX, L_MAX, L_PARAM, L_SUCC, L_ZERO};

impl Store {
    /// Interns a level node `(tag, a, b)`, computing its metadata from the children.
    pub(crate) fn intern_level(&mut self, tag: u8, a: u32, b: u32) -> LevelId {
        let n = LNode { tag, a, b };
        match self.level_tab.find(hash_lnode(&n), |id| self.lnodes[id as usize] == n) {
            Ok(id) => id,
            Err(slot) => {
                let meta = match tag {
                    L_ZERO => LMeta { has_param: false, never_zero: false, has_imax: false },
                    L_SUCC => {
                        let ma = self.lmeta[a as usize];
                        LMeta { has_param: ma.has_param, never_zero: true, has_imax: ma.has_imax }
                    }
                    L_MAX => {
                        let (ma, mb) = (self.lmeta[a as usize], self.lmeta[b as usize]);
                        LMeta {
                            has_param: ma.has_param || mb.has_param,
                            never_zero: ma.never_zero || mb.never_zero,
                            has_imax: ma.has_imax || mb.has_imax,
                        }
                    }
                    L_IMAX => {
                        let (ma, mb) = (self.lmeta[a as usize], self.lmeta[b as usize]);
                        LMeta {
                            has_param: ma.has_param || mb.has_param,
                            never_zero: mb.never_zero,
                            has_imax: true,
                        }
                    }
                    _ => LMeta { has_param: true, never_zero: false, has_imax: false },
                };
                let id = self.lnodes.len() as u32;
                self.lnodes.push(n);
                self.lmeta.push(meta);
                self.level_tab.insert_at(slot, id, hash_lnode(&n));
                id
            }
        }
    }

    pub fn mk_zero(&mut self) -> LevelId {
        self.intern_level(L_ZERO, 0, 0)
    }

    pub fn mk_succ(&mut self, l: LevelId) -> LevelId {
        self.intern_level(L_SUCC, l, 0)
    }

    pub fn mk_param(&mut self, name: NameId) -> LevelId {
        self.intern_level(L_PARAM, name, 0)
    }

    /// `succ^n zero`.
    pub fn mk_level_nat(&mut self, n: u32) -> LevelId {
        let mut l = self.mk_zero();
        for _ in 0..n {
            l = self.mk_succ(l);
        }
        l
    }

    /// Strips the outer successors: `succ^k base`.
    #[inline]
    fn level_strip(&self, mut l: LevelId) -> (LevelId, u32) {
        let mut k = 0;
        while self.lnodes[l as usize].tag == L_SUCC {
            l = self.lnodes[l as usize].a;
            k += 1;
        }
        (l, k)
    }

    /// `max` with the simplifications: `max(a,a)=a`, `max(0,a)=a`, and
    /// `max(succ^m x, succ^n x) = succ^max(m,n) x`; operands ordered by id.
    pub fn mk_max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        if a == b {
            return a;
        }
        if self.lnodes[a as usize].tag == L_ZERO {
            return b;
        }
        if self.lnodes[b as usize].tag == L_ZERO {
            return a;
        }
        let (ba, ka) = self.level_strip(a);
        let (bb, kb) = self.level_strip(b);
        if ba == bb {
            return if ka >= kb { a } else { b };
        }
        let (x, y) = if a < b { (a, b) } else { (b, a) };
        self.intern_level(L_MAX, x, y)
    }

    /// `imax a b`: `b = 0` gives `0`; `b` never zero gives `max a b`; `a = 0` gives `b`;
    /// `a = b` gives `a`.
    pub fn mk_imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        if self.lnodes[b as usize].tag == L_ZERO {
            return b;
        }
        if self.lmeta[b as usize].never_zero {
            return self.mk_max(a, b);
        }
        if self.lnodes[a as usize].tag == L_ZERO {
            return b;
        }
        if a == b {
            return a;
        }
        self.intern_level(L_IMAX, a, b)
    }

    #[inline]
    pub fn level(&self, l: LevelId) -> Level {
        let n = self.lnodes[l as usize];
        match n.tag {
            L_ZERO => Level::Zero,
            L_SUCC => Level::Succ(n.a),
            L_MAX => Level::Max(n.a, n.b),
            L_IMAX => Level::IMax(n.a, n.b),
            _ => Level::Param(n.a),
        }
    }

    #[inline]
    pub fn level_has_param(&self, l: LevelId) -> bool {
        self.lmeta[l as usize].has_param
    }

    /// Syntactic: the level is never zero under any assignment.
    #[inline]
    pub fn level_never_zero(&self, l: LevelId) -> bool {
        self.lmeta[l as usize].never_zero
    }

    #[inline]
    fn level_has_imax(&self, l: LevelId) -> bool {
        self.lmeta[l as usize].has_imax
    }

    /// Replaces `params[i]` by `levels[i]` (rebuilt through the smart constructors).
    pub fn level_subst(&mut self, l: LevelId, params: &[NameId], levels: &[LevelId]) -> LevelId {
        debug_assert_eq!(params.len(), levels.len());
        if !self.lmeta[l as usize].has_param {
            return l;
        }
        let n = self.lnodes[l as usize];
        match n.tag {
            L_PARAM => match params.iter().position(|&q| q == n.a) {
                Some(i) => levels[i],
                None => l,
            },
            L_SUCC => {
                let x = self.level_subst(n.a, params, levels);
                self.mk_succ(x)
            }
            L_MAX => {
                let x = self.level_subst(n.a, params, levels);
                let y = self.level_subst(n.b, params, levels);
                self.mk_max(x, y)
            }
            L_IMAX => {
                let x = self.level_subst(n.a, params, levels);
                let y = self.level_subst(n.b, params, levels);
                self.mk_imax(x, y)
            }
            _ => l,
        }
    }

    /// `level_eq(a, b)` iff `a <= b` and `b <= a` under every assignment.
    pub fn level_eq(&mut self, a: LevelId, b: LevelId) -> bool {
        a == b || (self.level_leq(a, b) && self.level_leq(b, a))
    }

    /// `l` is zero under every assignment.
    pub fn level_is_zero(&mut self, l: LevelId) -> bool {
        if self.level_never_zero(l) {
            return false;
        }
        let z = self.mk_zero();
        self.level_leq(l, z)
    }

    /// Complete decision procedure for `a <= b` under every assignment (DESIGN.md section 4).
    pub fn level_leq(&mut self, a: LevelId, b: LevelId) -> bool {
        if a == b {
            return true;
        }
        if let Some(&r) = self.leq_cache.get(&(a, b)) {
            return r;
        }
        let a1 = self.level_norm(a);
        let b1 = self.level_norm(b);
        let r = if a1 == b1 {
            true
        } else {
            let pa = self.find_imax_param(a1);
            let pb = self.find_imax_param(b1);
            match pa.or(pb) {
                Some(p) => {
                    // Case split on p: p = 0, or p = q + 1 for a fresh q (= p itself).
                    let z = self.mk_zero();
                    let pl = self.mk_param(p);
                    let s = self.mk_succ(pl);
                    let a0 = self.level_subst(a1, &[p], &[z]);
                    let b0 = self.level_subst(b1, &[p], &[z]);
                    let a1s = self.level_subst(a1, &[p], &[s]);
                    let b1s = self.level_subst(b1, &[p], &[s]);
                    self.level_leq(a0, b0) && self.level_leq(a1s, b1s)
                }
                None => self.leq_core(a1, b1, 0),
            }
        };
        self.leq_cache.insert((a, b), r);
        r
    }

    /// Rewrites so that `IMax` only occurs as `imax(u, Param p)`.
    fn level_norm(&mut self, l: LevelId) -> LevelId {
        if !self.level_has_imax(l) {
            return l;
        }
        let n = self.lnodes[l as usize];
        match n.tag {
            L_SUCC => {
                let x = self.level_norm(n.a);
                self.mk_succ(x)
            }
            L_MAX => {
                let x = self.level_norm(n.a);
                let y = self.level_norm(n.b);
                self.mk_max(x, y)
            }
            L_IMAX => {
                let x = self.level_norm(n.a);
                let y = self.level_norm(n.b);
                self.imax_dist(x, y)
            }
            _ => l,
        }
    }

    /// `imax(u, w)` for normalised `u`, `w`, distributing over `max` on the right
    /// (`imax(u, max(x,y)) = max(imax(u,x), imax(u,y))`) and over `imax` on the right
    /// (`imax(u, imax(v,q)) = max(imax(u,q), imax(v,q))`).
    fn imax_dist(&mut self, u: LevelId, w: LevelId) -> LevelId {
        let n = self.lnodes[w as usize];
        match n.tag {
            L_MAX => {
                let x = self.imax_dist(u, n.a);
                let y = self.imax_dist(u, n.b);
                self.mk_max(x, y)
            }
            L_IMAX => {
                let x = self.imax_dist(u, n.b);
                let y = self.imax_dist(n.a, n.b);
                self.mk_max(x, y)
            }
            _ => self.mk_imax(u, w),
        }
    }

    /// A parameter `p` such that `imax(_, p)` occurs in `l` (normalised input).
    fn find_imax_param(&self, l: LevelId) -> Option<NameId> {
        if !self.level_has_imax(l) {
            return None;
        }
        let n = self.lnodes[l as usize];
        match n.tag {
            L_SUCC => self.find_imax_param(n.a),
            L_MAX => self.find_imax_param(n.a).or_else(|| self.find_imax_param(n.b)),
            L_IMAX => {
                let r = self.lnodes[n.b as usize];
                debug_assert_eq!(r.tag, L_PARAM, "level_norm left an imax with a non-param right side");
                Some(r.a)
            }
            _ => None,
        }
    }

    /// Value of `l` with every parameter 0 (`l` must be imax-free).
    fn eval_at_zero(&self, l: LevelId) -> i64 {
        let n = self.lnodes[l as usize];
        match n.tag {
            L_SUCC => self.eval_at_zero(n.a) + 1,
            L_MAX => self.eval_at_zero(n.a).max(self.eval_at_zero(n.b)),
            _ => 0,
        }
    }

    /// Whether `b + k` has an atom `p + c` with `c + k >= 0` (`b` imax-free, `c` = succs so far).
    fn has_good_atom(&self, b: LevelId, p: NameId, c: i64, k: i64) -> bool {
        let n = self.lnodes[b as usize];
        match n.tag {
            L_PARAM => n.a == p && c + k >= 0,
            L_SUCC => self.has_good_atom(n.a, p, c + 1, k),
            L_MAX => self.has_good_atom(n.a, p, c, k) || self.has_good_atom(n.b, p, c, k),
            _ => false,
        }
    }

    /// Decides `a <= b + k` for imax-free `a`, `b` (DESIGN.md section 4, step 2).
    fn leq_core(&mut self, a: LevelId, b: LevelId, k: i64) -> bool {
        let na = self.lnodes[a as usize];
        match na.tag {
            L_MAX => self.leq_core(na.a, b, k) && self.leq_core(na.b, b, k),
            L_SUCC => self.leq_core(na.a, b, k - 1),
            _ => {
                let nb = self.lnodes[b as usize];
                if nb.tag == L_SUCC {
                    return self.leq_core(a, nb.a, k + 1);
                }
                match na.tag {
                    L_ZERO => self.eval_at_zero(b) + k >= 0,
                    L_PARAM => self.has_good_atom(b, na.a, 0, k),
                    _ => unreachable!("leq_core: imax survived normalisation"),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::Level;

    /// Deterministic xorshift generator.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Parameters u, v, w have names 1, 2, 3.
    fn eval(s: &Store, l: LevelId, asg: [u64; 3]) -> u64 {
        match s.level(l) {
            Level::Zero => 0,
            Level::Succ(x) => eval(s, x, asg) + 1,
            Level::Max(x, y) => eval(s, x, asg).max(eval(s, y, asg)),
            Level::IMax(x, y) => {
                let vy = eval(s, y, asg);
                if vy == 0 {
                    0
                } else {
                    eval(s, x, asg).max(vy)
                }
            }
            Level::Param(p) => asg[(p - 1) as usize],
        }
    }

    fn assignments(n: u64) -> Vec<[u64; 3]> {
        let mut v = Vec::new();
        for x in 0..n {
            for y in 0..n {
                for z in 0..n {
                    v.push([x, y, z]);
                }
            }
        }
        v
    }

    fn gen(s: &mut Store, rng: &mut Rng, depth: u32) -> LevelId {
        let r = rng.below(10);
        if depth == 0 || r < 3 {
            if rng.below(4) == 0 {
                s.mk_zero()
            } else {
                let p = 1 + rng.below(3) as NameId;
                s.mk_param(p)
            }
        } else if r < 5 {
            let x = gen(s, rng, depth - 1);
            s.mk_succ(x)
        } else if r < 8 {
            let x = gen(s, rng, depth - 1);
            let y = gen(s, rng, depth - 1);
            s.mk_max(x, y)
        } else {
            let x = gen(s, rng, depth - 1);
            let y = gen(s, rng, depth - 1);
            s.mk_imax(x, y)
        }
    }

    fn param(s: &mut Store, p: NameId) -> LevelId {
        s.mk_param(p)
    }

    #[test]
    fn smart_constructors_basic_shapes() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let u = param(&mut s, 1);
        let v = param(&mut s, 2);
        let one = s.mk_level_nat(1);
        let two = s.mk_level_nat(2);
        assert_eq!(s.mk_level_nat(2), two);
        assert_eq!(s.mk_max(u, u), u);
        assert_eq!(s.mk_max(z, u), u);
        assert_eq!(s.mk_max(u, z), u);
        assert_eq!(s.mk_max(one, two), two);
        assert_eq!(s.mk_max(two, one), two);
        assert_eq!(s.mk_max(u, v), s.mk_max(v, u));
        let su = s.mk_succ(u);
        let s2u = s.mk_succ(su);
        assert_eq!(s.mk_max(su, s2u), s2u);
        assert_eq!(s.mk_imax(u, z), z);
        assert_eq!(s.mk_imax(z, v), v);
        assert_eq!(s.mk_imax(u, u), u);
        assert_eq!(s.mk_imax(u, one), s.mk_max(u, one));
        let sv = s.mk_succ(v);
        assert_eq!(s.mk_imax(u, sv), s.mk_max(u, sv));
        assert!(s.level_never_zero(one));
        assert!(!s.level_never_zero(u));
        let m_u_one = s.mk_max(u, one);
        assert!(s.level_never_zero(m_u_one));
        let m_uv = s.mk_max(u, v);
        assert!(!s.level_never_zero(m_uv));
        let i_u_one = s.mk_imax(u, one);
        assert!(s.level_never_zero(i_u_one));
        let i_one_u = s.mk_imax(one, u);
        assert!(!s.level_never_zero(i_one_u));
        assert!(s.level_has_param(u));
        assert!(!s.level_has_param(two));
        assert_eq!(s.level(z), Level::Zero);
        assert_eq!(s.level(su), Level::Succ(u));
        assert_eq!(s.level(u), Level::Param(1));
    }

    #[test]
    fn regressions_leq_and_eq() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let one = s.mk_level_nat(1);
        let u = param(&mut s, 1);
        let v = param(&mut s, 2);
        let imax_uv = s.mk_imax(u, v);
        let su_imax = s.mk_succ(imax_uv);
        // succ(imax(u,v)) <= imax(u,v) is false
        assert!(!s.level_leq(su_imax, imax_uv));
        // imax(0, v) and succ(imax(0, v)) are not equal
        let imax_0v = s.mk_imax(z, v);
        let s_imax_0v = s.mk_succ(imax_0v);
        assert!(!s.level_eq(imax_0v, s_imax_0v));
        // imax(1, 0) equals zero
        let i10 = s.mk_imax(one, z);
        assert_eq!(i10, z);
        assert!(s.level_eq(i10, z));
        // imax(u, v+1) == max(u, v+1)
        let sv = s.mk_succ(v);
        assert_eq!(s.mk_imax(u, sv), s.mk_max(u, sv));
        // imax u v == imax (imax u v) v
        let rhs = s.mk_imax(imax_uv, v);
        assert!(s.level_eq(imax_uv, rhs));
        // max(u,v) == max(v,u)
        assert_eq!(s.mk_max(u, v), s.mk_max(v, u));
        // u <= max(u,v)
        let muv = s.mk_max(u, v);
        assert!(s.level_leq(u, muv));
        // u+1 <= max(u,v)+1
        let su = s.mk_succ(u);
        let smuv = s.mk_succ(muv);
        assert!(s.level_leq(su, smuv));
        // not u <= v
        assert!(!s.level_leq(u, v));
        // not u+1 <= u
        assert!(!s.level_leq(su, u));
        // 0 <= u
        assert!(s.level_leq(z, u));
        // not 1 <= u
        assert!(!s.level_leq(one, u));
        // imax(u,u) == u
        let iuu = s.mk_imax(u, u);
        assert_eq!(iuu, u);
        // is_zero
        assert!(s.level_is_zero(z));
        assert!(!s.level_is_zero(u));
        assert!(!s.level_is_zero(one));
        let i_u_z = s.mk_imax(u, z);
        assert!(s.level_is_zero(i_u_z));
        // imax(u, imax(v, w)) == max(imax(u,w), imax(v,w)) semantically
        let w = param(&mut s, 3);
        let iw = s.mk_imax(v, w);
        let lhs = s.mk_imax(u, iw);
        let a1 = s.mk_imax(u, w);
        let a2 = s.mk_imax(v, w);
        let rhs = s.mk_max(a1, a2);
        assert!(s.level_eq(lhs, rhs));
        // imax(u, v) <= max(u, v); imax(u, v+1) = max(u, v+1) >= 1; imax(u, v) is not 0
        assert!(s.level_leq(imax_uv, muv));
        let i_u_sv = s.mk_imax(u, sv);
        assert!(s.level_leq(one, i_u_sv));
        assert!(!s.level_leq(imax_uv, z));
    }

    #[test]
    fn smart_constructors_preserve_semantics() {
        let mut s = Store::new();
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        let asgs = assignments(5);
        for _ in 0..5_000 {
            let a = gen(&mut s, &mut rng, 4);
            let b = gen(&mut s, &mut rng, 4);
            let sa = s.mk_succ(a);
            let mab = s.mk_max(a, b);
            let iab = s.mk_imax(a, b);
            // level_subst of param 1 by b must be the semantic substitution
            let sub = s.level_subst(a, &[1], &[b]);
            for &g in &asgs {
                let (ea, eb) = (eval(&s, a, g), eval(&s, b, g));
                assert_eq!(eval(&s, sa, g), ea + 1);
                assert_eq!(eval(&s, mab, g), ea.max(eb));
                let want_imax = if eb == 0 { 0 } else { ea.max(eb) };
                assert_eq!(eval(&s, iab, g), want_imax, "imax({a},{b}) at {:?}", g);
                let mut g2 = g;
                g2[0] = eb;
                assert_eq!(eval(&s, sub, g), eval(&s, a, g2), "subst at {:?}", g);
            }
        }
    }

    #[test]
    fn leq_is_sound_and_complete_on_random_pairs() {
        let mut s = Store::new();
        let mut rng = Rng(0x2545_F491_4F6C_DD1D);
        let small = assignments(5);
        let big = assignments(7);
        let (mut n_true, mut n_false) = (0u32, 0u32);
        for i in 0..20_000 {
            let a = gen(&mut s, &mut rng, 5);
            let b = gen(&mut s, &mut rng, 5);
            let r = s.level_leq(a, b);
            if r {
                n_true += 1;
                // soundness: must hold on every sampled assignment
                for &g in &small {
                    assert!(
                        eval(&s, a, g) <= eval(&s, b, g),
                        "UNSOUND leq at pair {i}: a={:?} b={:?} at {:?}",
                        s.level(a),
                        s.level(b),
                        g
                    );
                }
            } else {
                n_false += 1;
                // completeness (expected): some assignment in {0..6}^3 refutes it
                let refuted = big.iter().any(|&g| eval(&s, a, g) > eval(&s, b, g));
                assert!(refuted, "possible incompleteness at pair {i}: a={:?} b={:?}", s.level(a), s.level(b));
            }
        }
        assert!(n_true > 1000 && n_false > 1000, "poor distribution: {n_true} true / {n_false} false");
    }

    #[test]
    fn level_eq_matches_semantics_on_random_pairs() {
        let mut s = Store::new();
        let mut rng = Rng(0x0123_4567_89AB_CDEF);
        let big = assignments(7);
        for _ in 0..5_000 {
            let a = gen(&mut s, &mut rng, 4);
            let b = gen(&mut s, &mut rng, 4);
            let sem = big.iter().all(|&g| eval(&s, a, g) == eval(&s, b, g));
            let eq = s.level_eq(a, b);
            if eq {
                assert!(sem, "UNSOUND eq: {:?} vs {:?}", s.level(a), s.level(b));
            }
        }
    }
}

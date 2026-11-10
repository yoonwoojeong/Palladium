//! Hash-consed terms, universe-level lists, typed locals, and substitution.
//! See docs/DESIGN.md section 4. Universe-level smart constructors and the leq/eq
//! decision procedure live in `level.rs`.
//!
//! Id 0 is a reserved dummy in the term, level and local tables, so that 0 can mean
//! "empty slot" in the open-addressing tables. `LevelsId` 0 is the empty list.

use crate::bignat::BigNat;
use crate::env::NameId;
use crate::util::{mix, FxHashMap};

pub type TermId = u32;

/// `instantiate` memoises shared subterms only after this many visited nodes: most calls are
/// small (a few dozen nodes) and their memo traffic costs more than the sharing it finds.
const INST_MEMO_AFTER: u32 = 64;
pub type LevelId = u32;
pub type LocalId = u32;
pub type LevelsId = u32;
pub type NatId = u32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Term {
    BVar(u32),
    Local(LocalId),
    Sort(LevelId),
    Const(NameId, LevelsId),
    App(TermId, TermId),
    Lam(TermId, TermId),
    Pi(TermId, TermId),
    Let(TermId, TermId, TermId),
    Proj(NameId, u32, TermId),
    Nat(NatId),
    Str(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

// Term node tags.
pub(crate) const T_DUMMY: u8 = 0;
pub(crate) const T_BVAR: u8 = 1;
pub(crate) const T_LOCAL: u8 = 2;
pub(crate) const T_SORT: u8 = 3;
pub(crate) const T_CONST: u8 = 4;
pub(crate) const T_APP: u8 = 5;
pub(crate) const T_LAM: u8 = 6;
pub(crate) const T_PI: u8 = 7;
pub(crate) const T_LET: u8 = 8;
pub(crate) const T_PROJ: u8 = 9;
pub(crate) const T_NAT: u8 = 10;
pub(crate) const T_STR: u8 = 11;

// Level node tags.
pub(crate) const L_DUMMY: u8 = 0;
pub(crate) const L_ZERO: u8 = 1;
pub(crate) const L_SUCC: u8 = 2;
pub(crate) const L_MAX: u8 = 3;
pub(crate) const L_IMAX: u8 = 4;
pub(crate) const L_PARAM: u8 = 5;

/// Compact term node: `a`, `b`, `c` are child ids or payload (see `Store::get`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Node {
    pub(crate) tag: u8,
    pub(crate) a: u32,
    pub(crate) b: u32,
    pub(crate) c: u32,
}

/// Per-term metadata, computed at construction.
#[derive(Clone, Copy)]
pub(crate) struct Meta {
    pub(crate) lbr: u32,
    pub(crate) local_ub: u32,
    pub(crate) has_param: bool,
}

const META_LEAF: Meta = Meta { lbr: 0, local_ub: 0, has_param: false };

/// A stored term: its node and its metadata in one record (one cache line per visit).
#[derive(Clone, Copy)]
pub(crate) struct Entry {
    pub(crate) tag: u8,
    pub(crate) has_param: bool,
    pub(crate) lbr: u32,
    pub(crate) local_ub: u32,
    pub(crate) a: u32,
    pub(crate) b: u32,
    pub(crate) c: u32,
}

impl Entry {
    #[inline]
    fn same_node(&self, n: &Node) -> bool {
        self.tag == n.tag && self.a == n.a && self.b == n.b && self.c == n.c
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct LNode {
    pub(crate) tag: u8,
    pub(crate) a: u32,
    pub(crate) b: u32,
}

#[derive(Clone, Copy)]
pub(crate) struct LMeta {
    pub(crate) has_param: bool,
    pub(crate) never_zero: bool,
    pub(crate) has_imax: bool,
}

#[inline]
fn hash_node(n: &Node) -> u32 {
    mix(((n.tag as u64) << 32) | n.a as u64, ((n.b as u64) << 32) | n.c as u64) as u32
}

#[inline]
pub(crate) fn hash_lnode(n: &LNode) -> u32 {
    mix(((n.tag as u64) << 32) | n.a as u64, n.b as u64) as u32
}

#[inline]
fn hash_local(depth: u32, ty: TermId) -> u32 {
    mix(depth as u64, ty as u64) as u32
}

#[inline]
fn hash_list(ls: &[LevelId]) -> u32 {
    let mut h = ls.len() as u64;
    for &l in ls {
        h = mix(h, l as u64);
    }
    h as u32
}

#[inline]
fn memo_key(t: TermId, off: u32) -> u64 {
    ((t as u64) << 32) | off as u64
}

/// Open-addressing (linear probing) set of ids, load factor at most 1/2. Each slot packs
/// the 32-bit hash of its id with the id (`hash << 32 | id`; `0` = empty, ids are >= 1), so
/// probes reject most mismatches without touching the node arrays.
pub(crate) struct Table {
    slots: Vec<u64>,
    len: usize,
}

impl Table {
    pub(crate) fn new() -> Table {
        Table { slots: vec![0; 64], len: 0 }
    }

    pub(crate) fn clear(&mut self) {
        self.slots.fill(0);
        self.len = 0;
    }

    /// Probes for an entry with hash `h` satisfying `eq`. `Err(slot)` gives the empty
    /// slot where it would be inserted.
    #[inline]
    pub(crate) fn find(&self, h: u32, eq: impl Fn(u32) -> bool) -> Result<u32, usize> {
        let mask = self.slots.len() - 1;
        let mut i = h as usize & mask;
        loop {
            let s = self.slots[i];
            if s == 0 {
                return Err(i);
            }
            if (s >> 32) as u32 == h {
                let id = s as u32;
                if eq(id) {
                    return Ok(id);
                }
            }
            i = (i + 1) & mask;
        }
    }

    /// Inserts `id` (hash `h`) into the empty `slot` returned by `find`, growing first if
    /// the load factor would exceed 1/2.
    #[inline]
    pub(crate) fn insert_at(&mut self, slot: usize, id: u32, h: u32) {
        let packed = ((h as u64) << 32) | id as u64;
        if (self.len + 1) * 4 > self.slots.len() * 3 {
            let new_cap = self.slots.len() * 2;
            let old = std::mem::replace(&mut self.slots, vec![0; new_cap]);
            for s in old.into_iter().filter(|&x| x != 0) {
                place(&mut self.slots, (s >> 32) as u32, s);
            }
            place(&mut self.slots, h, packed);
        } else {
            self.slots[slot] = packed;
        }
        self.len += 1;
    }
}

#[inline]
fn place(slots: &mut [u64], h: u32, packed: u64) {
    let mask = slots.len() - 1;
    let mut i = h as usize & mask;
    while slots[i] != 0 {
        i = (i + 1) & mask;
    }
    slots[i] = packed;
}

/// Exact memo table `(key -> u32)` with O(1) logical clear: an entry is live only if its
/// generation equals the current one, and `begin` bumps the generation. Open addressing
/// with linear probing; the table doubles when half full (within a traversal too), so no
/// result of the current traversal is ever dropped unless `MEMO_MAX` is reached.
#[derive(Clone, Copy, Default)]
pub(crate) struct MemoEnt {
    key: u64,
    val: u32,
    gen: u32,
}

const MEMO_MIN: usize = 1 << 10;
const MEMO_MAX: usize = 1 << 22;

pub(crate) struct Memo {
    ents: Vec<MemoEnt>,
    gen: u32,
    live: usize,
}

impl Memo {
    fn new() -> Self {
        Memo { ents: vec![MemoEnt::default(); MEMO_MIN], gen: 0, live: 0 }
    }
    /// Starts a new traversal: all previous entries become dead.
    #[inline]
    fn begin(&mut self) {
        self.gen = self.gen.wrapping_add(1);
        self.live = 0;
        if self.gen == 0 {
            self.ents.fill(MemoEnt::default());
            self.gen = 1;
        }
    }
    /// Drops every entry in O(1) (a generation bump; the table is zeroed only on wrap-around).
    fn clear(&mut self) {
        self.begin();
    }
    #[inline]
    fn slot(key: u64, mask: usize) -> usize {
        (key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize & mask
    }
    #[inline]
    fn get(&self, k: u64) -> Option<u32> {
        let mask = self.ents.len() - 1;
        let mut i = Self::slot(k, mask);
        loop {
            let e = self.ents[i];
            if e.gen != self.gen {
                return None;
            }
            if e.key == k {
                return Some(e.val);
            }
            i = (i + 1) & mask;
        }
    }
    #[inline]
    fn put(&mut self, k: u64, r: u32) {
        if (self.live + 1) * 2 > self.ents.len() {
            if self.ents.len() >= MEMO_MAX {
                return; // lossy at the limit: only costs recomputation
            }
            self.grow();
        }
        let mask = self.ents.len() - 1;
        let mut i = Self::slot(k, mask);
        loop {
            let e = self.ents[i];
            if e.gen != self.gen {
                self.ents[i] = MemoEnt { key: k, val: r, gen: self.gen };
                self.live += 1;
                return;
            }
            if e.key == k {
                self.ents[i].val = r;
                return;
            }
            i = (i + 1) & mask;
        }
    }
    fn grow(&mut self) {
        let n = self.ents.len() * 2;
        let old = std::mem::replace(&mut self.ents, vec![MemoEnt::default(); n]);
        let mask = n - 1;
        for e in old.into_iter().filter(|e| e.gen == self.gen) {
            let mut i = Self::slot(e.key, mask);
            while self.ents[i].gen == self.gen {
                i = (i + 1) & mask;
            }
            self.ents[i] = e;
        }
    }
}

/// Context of one `abstract_locals` call.
struct AbsCtx<'a> {
    locals: &'a [TermId],
    index: Option<FxHashMap<TermId, u32>>,
    min_depth: u32,
    n: u32,
}

impl<'a> AbsCtx<'a> {
    #[inline]
    fn pos(&self, t: TermId) -> Option<u32> {
        match &self.index {
            Some(m) => m.get(&t).copied(),
            None => self.locals.iter().position(|&l| l == t).map(|j| j as u32),
        }
    }
}

/// Hash-consed store of terms, universe levels, universe-level lists, locals and nat
/// literals. Every node carries its metadata (`lbr`, `local_ub`, `has_param`).
pub struct Store {
    pub(crate) nodes: Vec<Entry>,
    pub(crate) term_tab: Table,
    pub(crate) lnodes: Vec<LNode>,
    pub(crate) lmeta: Vec<LMeta>,
    pub(crate) level_tab: Table,
    pub(crate) list_start: Vec<u32>,
    pub(crate) list_len: Vec<u32>,
    pub(crate) list_has_param: Vec<bool>,
    pub(crate) list_data: Vec<LevelId>,
    pub(crate) list_tab: Table,
    pub(crate) local_depth: Vec<u32>,
    pub(crate) local_ty: Vec<TermId>,
    pub(crate) local_tab: Table,
    pub(crate) nat_vals: Vec<BigNat>,
    pub(crate) nat_map: FxHashMap<BigNat, NatId>,
    pub(crate) inst_memo: Memo,
    /// Nodes visited by the current `instantiate`; the memo is used only past `INST_MEMO_AFTER`.
    inst_steps: u32,
    pub(crate) abs_memo: Memo,
    pub(crate) subst_memo: Memo,
    /// Shared stack for application spines during substitution (used with a base index).
    spine: Vec<TermId>,
    pub(crate) leq_cache: FxHashMap<(LevelId, LevelId), bool>,
}

impl Default for Store {
    fn default() -> Self {
        Store::new()
    }
}

impl Store {
    pub fn new() -> Store {
        let mut s = Store {
            nodes: Vec::new(),
            term_tab: Table::new(),
            lnodes: Vec::new(),
            lmeta: Vec::new(),
            level_tab: Table::new(),
            list_start: Vec::new(),
            list_len: Vec::new(),
            list_has_param: Vec::new(),
            list_data: Vec::new(),
            list_tab: Table::new(),
            local_depth: Vec::new(),
            local_ty: Vec::new(),
            local_tab: Table::new(),
            nat_vals: Vec::new(),
            nat_map: FxHashMap::default(),
            inst_memo: Memo::new(),
            inst_steps: 0,
            abs_memo: Memo::new(),
            subst_memo: Memo::new(),
            spine: Vec::new(),
            leq_cache: FxHashMap::default(),
        };
        s.clear();
        s
    }

    /// Drops every node, keeping allocations.
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.nodes.push(Entry { tag: T_DUMMY, has_param: false, lbr: 0, local_ub: 0, a: 0, b: 0, c: 0 });
        self.term_tab.clear();
        self.lnodes.clear();
        self.lnodes.push(LNode { tag: L_DUMMY, a: 0, b: 0 });
        self.lmeta.clear();
        self.lmeta.push(LMeta { has_param: false, never_zero: false, has_imax: false });
        self.level_tab.clear();
        self.list_start.clear();
        self.list_start.push(0);
        self.list_len.clear();
        self.list_len.push(0);
        self.list_has_param.clear();
        self.list_has_param.push(false);
        self.list_data.clear();
        self.list_tab.clear();
        self.local_depth.clear();
        self.local_depth.push(0);
        self.local_ty.clear();
        self.local_ty.push(0);
        self.local_tab.clear();
        self.nat_vals.clear();
        self.nat_map.clear();
        self.inst_memo.clear();
        self.abs_memo.clear();
        self.subst_memo.clear();
        self.spine.clear();
        self.leq_cache.clear();
    }

    /// Number of terms interned so far (excluding the dummy).
    pub fn num_terms(&self) -> usize {
        self.nodes.len() - 1
    }

    // ----- accessors -------------------------------------------------------------

    #[inline]
    pub fn get(&self, t: TermId) -> Term {
        let n = self.nodes[t as usize];
        match n.tag {
            T_BVAR => Term::BVar(n.a),
            T_LOCAL => Term::Local(n.a),
            T_SORT => Term::Sort(n.a),
            T_CONST => Term::Const(n.a, n.b),
            T_APP => Term::App(n.a, n.b),
            T_LAM => Term::Lam(n.a, n.b),
            T_PI => Term::Pi(n.a, n.b),
            T_LET => Term::Let(n.a, n.b, n.c),
            T_PROJ => Term::Proj(n.a, n.b, n.c),
            T_NAT => Term::Nat(n.a),
            T_STR => Term::Str(n.a),
            _ => unreachable!("dummy term id {t} used"),
        }
    }

    /// Loose bound variable range: 0 means closed.
    #[inline]
    pub fn lbr(&self, t: TermId) -> u32 {
        self.nodes[t as usize].lbr
    }

    /// 0 if the term contains no locals, else 1 + the largest local depth occurring in it.
    #[inline]
    pub fn local_ub(&self, t: TermId) -> u32 {
        self.nodes[t as usize].local_ub
    }

    #[inline]
    pub fn has_param(&self, t: TermId) -> bool {
        self.nodes[t as usize].has_param
    }

    #[inline]
    pub fn is_closed(&self, t: TermId) -> bool {
        self.nodes[t as usize].lbr == 0
    }

    #[inline]
    pub fn has_loose_bvars(&self, t: TermId) -> bool {
        self.nodes[t as usize].lbr > 0
    }

    pub fn nat_value(&self, id: NatId) -> &BigNat {
        &self.nat_vals[id as usize]
    }

    pub fn local_depth(&self, id: LocalId) -> u32 {
        self.local_depth[id as usize]
    }

    pub fn local_type(&self, id: LocalId) -> TermId {
        self.local_ty[id as usize]
    }

    /// The level list of a `LevelsId` (`0` is the empty list).
    #[inline]
    pub fn levels(&self, id: LevelsId) -> &[LevelId] {
        let s = self.list_start[id as usize] as usize;
        let n = self.list_len[id as usize] as usize;
        &self.list_data[s..s + n]
    }

    // ----- interning -------------------------------------------------------------

    #[inline]
    fn intern_term(&mut self, n: Node, m: Meta) -> TermId {
        match self.term_tab.find(hash_node(&n), |id| self.nodes[id as usize].same_node(&n)) {
            Ok(id) => id,
            Err(slot) => {
                let id = self.nodes.len() as u32;
                self.nodes.push(Entry {
                    tag: n.tag,
                    has_param: m.has_param,
                    lbr: m.lbr,
                    local_ub: m.local_ub,
                    a: n.a,
                    b: n.b,
                    c: n.c,
                });
                self.term_tab.insert_at(slot, id, hash_node(&n));
                id
            }
        }
    }

    // ----- term constructors -----------------------------------------------------

    #[inline]
    pub fn mk_bvar(&mut self, i: u32) -> TermId {
        self.intern_term(
            Node { tag: T_BVAR, a: i, b: 0, c: 0 },
            Meta { lbr: i.saturating_add(1), local_ub: 0, has_param: false },
        )
    }

    pub fn mk_sort(&mut self, l: LevelId) -> TermId {
        let hp = self.lmeta[l as usize].has_param;
        self.intern_term(
            Node { tag: T_SORT, a: l, b: 0, c: 0 },
            Meta { lbr: 0, local_ub: 0, has_param: hp },
        )
    }

    pub fn mk_const(&mut self, name: NameId, levels: LevelsId) -> TermId {
        let hp = self.list_has_param[levels as usize];
        self.intern_term(
            Node { tag: T_CONST, a: name, b: levels, c: 0 },
            Meta { lbr: 0, local_ub: 0, has_param: hp },
        )
    }

    #[inline]
    pub fn mk_app(&mut self, f: TermId, a: TermId) -> TermId {
        let mf = self.nodes[f as usize];
        let ma = self.nodes[a as usize];
        let m = Meta {
            lbr: mf.lbr.max(ma.lbr),
            local_ub: mf.local_ub.max(ma.local_ub),
            has_param: mf.has_param || ma.has_param,
        };
        self.intern_term(Node { tag: T_APP, a: f, b: a, c: 0 }, m)
    }

    #[inline]
    pub fn mk_lam(&mut self, ty: TermId, body: TermId) -> TermId {
        let m = self.binder_meta(ty, body);
        self.intern_term(Node { tag: T_LAM, a: ty, b: body, c: 0 }, m)
    }

    #[inline]
    pub fn mk_pi(&mut self, ty: TermId, body: TermId) -> TermId {
        let m = self.binder_meta(ty, body);
        self.intern_term(Node { tag: T_PI, a: ty, b: body, c: 0 }, m)
    }

    #[inline]
    fn binder_meta(&self, ty: TermId, body: TermId) -> Meta {
        let mt = self.nodes[ty as usize];
        let mb = self.nodes[body as usize];
        Meta {
            lbr: mt.lbr.max(mb.lbr.saturating_sub(1)),
            local_ub: mt.local_ub.max(mb.local_ub),
            has_param: mt.has_param || mb.has_param,
        }
    }

    pub fn mk_let(&mut self, ty: TermId, val: TermId, body: TermId) -> TermId {
        let mt = self.nodes[ty as usize];
        let mv = self.nodes[val as usize];
        let mb = self.nodes[body as usize];
        let m = Meta {
            lbr: mt.lbr.max(mv.lbr).max(mb.lbr.saturating_sub(1)),
            local_ub: mt.local_ub.max(mv.local_ub).max(mb.local_ub),
            has_param: mt.has_param || mv.has_param || mb.has_param,
        };
        self.intern_term(Node { tag: T_LET, a: ty, b: val, c: body }, m)
    }

    pub fn mk_proj(&mut self, name: NameId, idx: u32, e: TermId) -> TermId {
        let me = Meta { lbr: self.nodes[e as usize].lbr, local_ub: self.nodes[e as usize].local_ub, has_param: self.nodes[e as usize].has_param };
        self.intern_term(Node { tag: T_PROJ, a: name, b: idx, c: e }, me)
    }

    /// Interns a nat literal and returns the term.
    pub fn mk_nat(&mut self, n: &BigNat) -> TermId {
        let id = match self.nat_map.get(n) {
            Some(&id) => id,
            None => {
                let id = self.nat_vals.len() as u32;
                self.nat_vals.push(n.clone());
                self.nat_map.insert(n.clone(), id);
                id
            }
        };
        self.mk_nat_id(id)
    }

    pub fn mk_nat_id(&mut self, id: NatId) -> TermId {
        self.intern_term(Node { tag: T_NAT, a: id, b: 0, c: 0 }, META_LEAF)
    }

    pub fn mk_nat_u64(&mut self, n: u64) -> TermId {
        self.mk_nat(&BigNat::from_u64(n))
    }

    pub fn mk_str(&mut self, idx: u32) -> TermId {
        self.intern_term(Node { tag: T_STR, a: idx, b: 0, c: 0 }, META_LEAF)
    }

    /// Interns the typed local `(depth, ty)`. Invariant L: `local_ub(ty) <= depth` and
    /// `ty` is closed. Both checks are kept in release builds.
    pub fn mk_local(&mut self, depth: u32, ty: TermId) -> TermId {
        assert!(self.local_ub(ty) <= depth, "mk_local: invariant L violated (type uses a deeper local)");
        assert!(self.is_closed(ty), "mk_local: local type has loose bound variables");
        let h = hash_local(depth, ty);
        let lid = match self
            .local_tab
            .find(h, |id| self.local_depth[id as usize] == depth && self.local_ty[id as usize] == ty)
        {
            Ok(id) => id,
            Err(slot) => {
                let id = self.local_depth.len() as u32;
                self.local_depth.push(depth);
                self.local_ty.push(ty);
                self.local_tab.insert_at(slot, id, h);
                id
            }
        };
        let hp = self.nodes[ty as usize].has_param;
        self.intern_term(
            Node { tag: T_LOCAL, a: lid, b: 0, c: 0 },
            Meta { lbr: 0, local_ub: depth.saturating_add(1), has_param: hp },
        )
    }

    // ----- level lists -----------------------------------------------------------

    /// Interns a universe-level list. The empty list is `0`.
    pub fn mk_levels(&mut self, ls: &[LevelId]) -> LevelsId {
        if ls.is_empty() {
            return 0;
        }
        let h = hash_list(ls);
        let found = self.list_tab.find(h, |id| {
            let s = self.list_start[id as usize] as usize;
            let n = self.list_len[id as usize] as usize;
            self.list_data[s..s + n] == *ls
        });
        match found {
            Ok(id) => id,
            Err(slot) => {
                let id = self.list_start.len() as u32;
                let start = self.list_data.len() as u32;
                self.list_data.extend_from_slice(ls);
                self.list_start.push(start);
                self.list_len.push(ls.len() as u32);
                let hp = ls.iter().any(|&l| self.lmeta[l as usize].has_param);
                self.list_has_param.push(hp);
                self.list_tab.insert_at(slot, id, h);
                id
            }
        }
    }

    // ----- applications ----------------------------------------------------------

    pub fn mk_app_n(&mut self, f: TermId, args: &[TermId]) -> TermId {
        let mut r = f;
        for &a in args {
            r = self.mk_app(r, a);
        }
        r
    }

    /// Splits `t` into head and arguments. Appends the arguments to `args` in application
    /// order (first argument first) and returns the head.
    pub fn unfold_app(&self, t: TermId, args: &mut Vec<TermId>) -> TermId {
        let start = args.len();
        let mut cur = t;
        while self.nodes[cur as usize].tag == T_APP {
            let n = self.nodes[cur as usize];
            args.push(n.b);
            cur = n.a;
        }
        args[start..].reverse();
        cur
    }

    /// The head of an application spine.
    pub fn app_fn(&self, t: TermId) -> TermId {
        let mut cur = t;
        while self.nodes[cur as usize].tag == T_APP {
            cur = self.nodes[cur as usize].a;
        }
        cur
    }

    pub fn app_num_args(&self, t: TermId) -> usize {
        let mut cur = t;
        let mut n = 0;
        while self.nodes[cur as usize].tag == T_APP {
            cur = self.nodes[cur as usize].a;
            n += 1;
        }
        n
    }

    // ----- instantiate -----------------------------------------------------------

    /// Simultaneous substitution of the outermost `xs.len()` loose bound variables.
    /// Loose bvar `i` becomes `xs[xs.len()-1-i]` if `i < xs.len()`, else `BVar(i - xs.len())`.
    /// All `xs` must be closed.
    pub fn instantiate(&mut self, t: TermId, xs: &[TermId]) -> TermId {
        if xs.is_empty() || self.nodes[t as usize].lbr == 0 {
            return t;
        }
        debug_assert!(xs.iter().all(|&x| self.is_closed(x)), "instantiate: open substitution");
        self.inst_memo.begin();
        self.inst_steps = 0;
        self.inst_rec(t, 0, xs)
    }

    fn inst_rec(&mut self, t: TermId, off: u32, xs: &[TermId]) -> TermId {
        if self.nodes[t as usize].lbr <= off {
            return t;
        }
        let n = self.nodes[t as usize];
        match n.tag {
            T_BVAR => {
                let k = n.a - off;
                let len = xs.len() as u32;
                if k < len {
                    xs[(len - 1 - k) as usize]
                } else {
                    self.mk_bvar(n.a - len)
                }
            }
            T_APP => self.inst_app(t, off, xs),
            T_LAM | T_PI | T_LET | T_PROJ => {
                self.inst_steps += 1;
                let memo = self.inst_steps > INST_MEMO_AFTER;
                let key = memo_key(t, off);
                if memo {
                    if let Some(r) = self.inst_memo.get(key) {
                        return r;
                    }
                }
                let r = match n.tag {
                    T_LAM => {
                        let ty = self.inst_rec(n.a, off, xs);
                        let b = self.inst_rec(n.b, off + 1, xs);
                        self.mk_lam(ty, b)
                    }
                    T_PI => {
                        let ty = self.inst_rec(n.a, off, xs);
                        let b = self.inst_rec(n.b, off + 1, xs);
                        self.mk_pi(ty, b)
                    }
                    T_LET => {
                        let ty = self.inst_rec(n.a, off, xs);
                        let v = self.inst_rec(n.b, off, xs);
                        let b = self.inst_rec(n.c, off + 1, xs);
                        self.mk_let(ty, v, b)
                    }
                    _ => {
                        let e = self.inst_rec(n.c, off, xs);
                        self.mk_proj(n.a, n.b, e)
                    }
                };
                if memo {
                    self.inst_memo.put(key, r);
                }
                r
            }
            _ => t,
        }
    }

    fn inst_app(&mut self, t: TermId, off: u32, xs: &[TermId]) -> TermId {
        self.inst_steps += 1;
        let memo = self.inst_steps > INST_MEMO_AFTER;
        let key = memo_key(t, off);
        if memo {
            if let Some(r) = self.inst_memo.get(key) {
                return r;
            }
        }
        let base_len = self.spine.len();
        let base = self.push_spine(t, |m| m.lbr > off);
        let mut r = self.inst_rec(base, off, xs);
        let mut i = self.spine.len();
        while i > base_len {
            i -= 1;
            let node = self.spine[i];
            let arg = self.nodes[node as usize].b;
            let ai = self.inst_rec(arg, off, xs);
            r = self.mk_app(r, ai);
            if memo && i == base_len {
                self.inst_memo.put(memo_key(node, off), r);
            }
        }
        self.spine.truncate(base_len);
        r
    }

    /// Walks the application spine starting at `t` (an App) while the function position is an
    /// App satisfying `keep`. Pushes every visited spine node onto `self.spine` (outermost
    /// first) and returns the first function-position term that is not collected. Callers
    /// pop back to their own base length, which keeps nested use of the stack correct.
    #[inline]
    fn push_spine(&mut self, t: TermId, keep: impl Fn(&Entry) -> bool) -> TermId {
        let mut cur = t;
        loop {
            self.spine.push(cur);
            let f = self.nodes[cur as usize].a;
            if self.nodes[f as usize].tag == T_APP && keep(&self.nodes[f as usize]) {
                cur = f;
            } else {
                return f;
            }
        }
    }

    // ----- abstract_locals -------------------------------------------------------

    /// Inverse of instantiation: `locals[j]` becomes `BVar(locals.len()-1-j + binder depth)`.
    /// The locals must be distinct `Local` terms.
    pub fn abstract_locals(&mut self, t: TermId, locals: &[TermId]) -> TermId {
        if locals.is_empty() || self.nodes[t as usize].local_ub == 0 {
            return t;
        }
        let mut min_depth = u32::MAX;
        for &l in locals {
            let n = self.nodes[l as usize];
            assert!(n.tag == T_LOCAL, "abstract_locals: argument is not a local");
            min_depth = min_depth.min(self.local_depth[n.a as usize]);
        }
        let index = if locals.len() > 8 {
            let mut m = FxHashMap::default();
            for (j, &l) in locals.iter().enumerate() {
                m.entry(l).or_insert(j as u32);
            }
            Some(m)
        } else {
            None
        };
        let ctx = AbsCtx { locals, index, min_depth, n: locals.len() as u32 };
        self.abs_memo.begin();
        self.abs_rec(t, 0, &ctx)
    }

    fn abs_rec(&mut self, t: TermId, off: u32, ctx: &AbsCtx) -> TermId {
        if self.nodes[t as usize].local_ub <= ctx.min_depth {
            return t;
        }
        let n = self.nodes[t as usize];
        match n.tag {
            T_LOCAL => match ctx.pos(t) {
                Some(j) => self.mk_bvar(ctx.n - 1 - j + off),
                None => t,
            },
            T_APP => self.abs_app(t, off, ctx),
            T_LAM | T_PI | T_LET | T_PROJ => {
                let key = memo_key(t, off);
                if let Some(r) = self.abs_memo.get(key) {
                    return r;
                }
                let r = match n.tag {
                    T_LAM => {
                        let ty = self.abs_rec(n.a, off, ctx);
                        let b = self.abs_rec(n.b, off + 1, ctx);
                        self.mk_lam(ty, b)
                    }
                    T_PI => {
                        let ty = self.abs_rec(n.a, off, ctx);
                        let b = self.abs_rec(n.b, off + 1, ctx);
                        self.mk_pi(ty, b)
                    }
                    T_LET => {
                        let ty = self.abs_rec(n.a, off, ctx);
                        let v = self.abs_rec(n.b, off, ctx);
                        let b = self.abs_rec(n.c, off + 1, ctx);
                        self.mk_let(ty, v, b)
                    }
                    _ => {
                        let e = self.abs_rec(n.c, off, ctx);
                        self.mk_proj(n.a, n.b, e)
                    }
                };
                self.abs_memo.put(key, r);
                r
            }
            _ => t,
        }
    }

    fn abs_app(&mut self, t: TermId, off: u32, ctx: &AbsCtx) -> TermId {
        let key = memo_key(t, off);
        if let Some(r) = self.abs_memo.get(key) {
            return r;
        }
        let min = ctx.min_depth;
        let base_len = self.spine.len();
        let base = self.push_spine(t, |m| m.local_ub > min);
        let mut r = self.abs_rec(base, off, ctx);
        let mut i = self.spine.len();
        while i > base_len {
            i -= 1;
            let node = self.spine[i];
            let arg = self.nodes[node as usize].b;
            let ai = self.abs_rec(arg, off, ctx);
            r = self.mk_app(r, ai);
            if i == base_len {
                self.abs_memo.put(memo_key(node, off), r);
            }
        }
        self.spine.truncate(base_len);
        r
    }

    // ----- subst_params ----------------------------------------------------------

    /// Replaces `Level::Param(params[i])` by the i-th level of `levels` in all sorts,
    /// constant level lists, and local types.
    pub fn subst_params(&mut self, t: TermId, params: &[NameId], levels: LevelsId) -> TermId {
        assert_eq!(
            params.len(),
            self.list_len[levels as usize] as usize,
            "subst_params: parameter/level count mismatch"
        );
        if params.is_empty() || !self.nodes[t as usize].has_param {
            return t;
        }
        let ls: Vec<LevelId> = self.levels(levels).to_vec();
        self.subst_memo.begin();
        self.subst_rec(t, params, &ls)
    }

    fn subst_rec(&mut self, t: TermId, params: &[NameId], ls: &[LevelId]) -> TermId {
        if !self.nodes[t as usize].has_param {
            return t;
        }
        let key = t as u64;
        if let Some(r) = self.subst_memo.get(key) {
            return r;
        }
        let n = self.nodes[t as usize];
        let r = match n.tag {
            T_SORT => {
                let l = self.level_subst(n.a, params, ls);
                self.mk_sort(l)
            }
            T_CONST => {
                let old: Vec<LevelId> = self.levels(n.b).to_vec();
                let mut new = Vec::with_capacity(old.len());
                for l in old {
                    new.push(self.level_subst(l, params, ls));
                }
                let lv = self.mk_levels(&new);
                self.mk_const(n.a, lv)
            }
            T_LOCAL => {
                let depth = self.local_depth[n.a as usize];
                let ty = self.local_ty[n.a as usize];
                let ty2 = self.subst_rec(ty, params, ls);
                self.mk_local(depth, ty2)
            }
            T_APP => self.subst_app(t, params, ls),
            T_LAM => {
                let ty = self.subst_rec(n.a, params, ls);
                let b = self.subst_rec(n.b, params, ls);
                self.mk_lam(ty, b)
            }
            T_PI => {
                let ty = self.subst_rec(n.a, params, ls);
                let b = self.subst_rec(n.b, params, ls);
                self.mk_pi(ty, b)
            }
            T_LET => {
                let ty = self.subst_rec(n.a, params, ls);
                let v = self.subst_rec(n.b, params, ls);
                let b = self.subst_rec(n.c, params, ls);
                self.mk_let(ty, v, b)
            }
            T_PROJ => {
                let e = self.subst_rec(n.c, params, ls);
                self.mk_proj(n.a, n.b, e)
            }
            _ => t,
        };
        self.subst_memo.put(key, r);
        r
    }

    fn subst_app(&mut self, t: TermId, params: &[NameId], ls: &[LevelId]) -> TermId {
        let base_len = self.spine.len();
        let base = self.push_spine(t, |m| m.has_param);
        let mut r = self.subst_rec(base, params, ls);
        let mut i = self.spine.len();
        while i > base_len {
            i -= 1;
            let node = self.spine[i];
            let arg = self.nodes[node as usize].b;
            let ai = self.subst_rec(arg, params, ls);
            r = self.mk_app(r, ai);
            if i == base_len {
                self.subst_memo.put(node as u64, r);
            }
        }
        self.spine.truncate(base_len);
        r
    }

    // ----- beta ------------------------------------------------------------------

    /// Beta-reduces `f` applied to `args` as far as `f` has lambdas, then re-applies the rest.
    pub fn beta(&mut self, f: TermId, args: &[TermId]) -> TermId {
        let mut f = f;
        let mut i = 0;
        while i < args.len() {
            let mut body = f;
            let mut n = 0;
            while i + n < args.len() {
                match self.get(body) {
                    Term::Lam(_, b) => {
                        body = b;
                        n += 1;
                    }
                    _ => break,
                }
            }
            if n == 0 {
                break;
            }
            f = self.instantiate(body, &args[i..i + n]);
            i += n;
        }
        self.mk_app_n(f, &args[i..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_big_stack<F: FnOnce() + Send + 'static>(f: F) {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn hash_consing_identity() {
        let mut s = Store::new();
        let a = s.mk_bvar(0);
        assert_eq!(a, s.mk_bvar(0));
        let b = s.mk_bvar(1);
        assert_ne!(a, b);
        let x = s.mk_app(a, b);
        assert_eq!(x, s.mk_app(a, b));
        assert_ne!(x, s.mk_app(b, a));
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let l1 = s.mk_lam(ty, a);
        assert_eq!(l1, s.mk_lam(ty, a));
        assert_ne!(l1, s.mk_pi(ty, a));
        let n1 = s.mk_nat_u64(5);
        let n2 = s.mk_nat(&BigNat::from_u64(5));
        assert_eq!(n1, n2);
        assert_ne!(n1, s.mk_nat_u64(6));
        assert_eq!(s.nat_value(match s.get(n1) { Term::Nat(i) => i, _ => panic!() }).to_u64(), Some(5));
        let c1 = s.mk_levels(&[z]);
        assert_eq!(c1, s.mk_levels(&[z]));
        assert_eq!(s.mk_levels(&[]), 0);
        assert!(s.levels(0).is_empty());
        assert_eq!(s.levels(c1), &[z]);
        let c_a = s.mk_const(7, c1);
        assert_eq!(c_a, s.mk_const(7, c1));
        assert_ne!(c_a, s.mk_const(8, c1));
        let p = s.mk_str(3);
        assert_eq!(p, s.mk_str(3));
        assert_eq!(s.get(p), Term::Str(3));
    }

    #[test]
    fn metadata_lbr_locals_params() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let b3 = s.mk_bvar(3);
        assert_eq!(s.lbr(b3), 4);
        assert!(!s.is_closed(b3));
        // lam(_, #1): body lbr 2, minus the binder -> 1
        let b1 = s.mk_bvar(1);
        let lb = s.mk_lam(ty, b1);
        assert_eq!(s.lbr(lb), 1);
        // lam(_, #0) is closed
        let b0 = s.mk_bvar(0);
        let closed = s.mk_lam(ty, b0);
        assert!(s.is_closed(closed));
        // binder type contributes too: pi(#2, #0) has lbr 3
        let b2 = s.mk_bvar(2);
        let pb = s.mk_pi(b2, b0);
        assert_eq!(s.lbr(pb), 3);
        // let(ty, #1, #2): max(0, 2, 2-1) = 2
        let b2b = s.mk_bvar(2);
        let lt = s.mk_let(ty, b1, b2b);
        assert_eq!(s.lbr(lt), 2);
        // proj over #5 has lbr 6
        let b5 = s.mk_bvar(5);
        let pr = s.mk_proj(9, 0, b5);
        assert_eq!(s.lbr(pr), 6);
        // no overflow on BVar(MAX)
        let big = s.mk_bvar(u32::MAX);
        assert_eq!(s.lbr(big), u32::MAX);
        let lb2 = s.mk_lam(ty, big);
        assert_eq!(s.lbr(lb2), u32::MAX - 1);

        // locals
        let l = s.mk_local(2, ty);
        assert_eq!(s.local_ub(l), 3);
        assert!(s.is_closed(l));
        assert!(!s.has_param(l));
        let app = s.mk_app(l, b3);
        assert_eq!(s.local_ub(app), 3);
        assert_eq!(s.lbr(app), 4);
        let lid = match s.get(l) {
            Term::Local(i) => i,
            _ => panic!(),
        };
        assert_eq!(s.local_depth(lid), 2);
        assert_eq!(s.local_type(lid), ty);
        assert_eq!(l, s.mk_local(2, ty));
        assert_ne!(l, s.mk_local(3, ty));

        // parameters
        let u = s.mk_param(1);
        let su = s.mk_sort(u);
        assert!(s.has_param(su));
        assert!(!s.has_param(ty));
        let lv = s.mk_levels(&[u]);
        let c4 = s.mk_const(4, lv);
        assert!(s.has_param(c4));
        let c4z = s.mk_const(4, 0);
        assert!(!s.has_param(c4z));
        let lam_u = s.mk_lam(su, b0);
        assert!(s.has_param(lam_u));
        // a local whose type mentions a parameter has has_param
        let lp = s.mk_local(0, su);
        assert!(s.has_param(lp));
    }

    #[test]
    #[should_panic(expected = "invariant L")]
    fn mk_local_checks_invariant_l() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let l2 = s.mk_local(2, ty);
        // closed type mentioning a depth-2 local: local_ub = 3 > depth 1
        let ty2 = s.mk_app(l2, l2);
        assert!(s.is_closed(ty2));
        s.mk_local(1, ty2);
    }

    #[test]
    #[should_panic(expected = "loose bound variables")]
    fn mk_local_rejects_open_type() {
        let mut s = Store::new();
        let b = s.mk_bvar(0);
        s.mk_local(0, b);
    }

    #[test]
    fn instantiate_basic_and_above_range() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let c1 = s.mk_const(1, 0);
        let c2 = s.mk_const(2, 0);
        // #0 #1 with [c1, c2]: #0 -> c2, #1 -> c1
        let t = {
            let b0 = s.mk_bvar(0);
            let b1 = s.mk_bvar(1);
            s.mk_app(b0, b1)
        };
        let expect = s.mk_app(c2, c1);
        assert_eq!(s.instantiate(t, &[c1, c2]), expect);
        // #0 #1 with [c1]: #0 -> c1, #1 -> #0 (lowered)
        let b0 = s.mk_bvar(0);
        let expect = s.mk_app(c1, b0);
        assert_eq!(s.instantiate(t, &[c1]), expect);
        // no loose bvars: identity
        assert_eq!(s.instantiate(c1, &[c2]), c1);
        // empty substitution: identity
        assert_eq!(s.instantiate(t, &[]), t);
        // under a binder: lam(ty, #1 #0) with [c1] -> lam(ty, c1 #0)
        let body = {
            let b1 = s.mk_bvar(1);
            let b0 = s.mk_bvar(0);
            s.mk_app(b1, b0)
        };
        let lam = s.mk_lam(ty, body);
        let expect_body = s.mk_app(c1, b0);
        let expect = s.mk_lam(ty, expect_body);
        assert_eq!(s.instantiate(lam, &[c1]), expect);
        // binder type is substituted at the outer level too
        let lam2 = {
            let b0 = s.mk_bvar(0);
            s.mk_lam(b0, b0)
        };
        let lam2_inst = {
            let b0 = s.mk_bvar(0);
            s.mk_lam(c1, b0)
        };
        assert_eq!(s.instantiate(lam2, &[c1]), lam2_inst);
    }

    #[test]
    fn instantiate_two_levels_of_binders() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let c = s.mk_const(1, 0);
        // lam(ty, lam(ty, #2 #1 #0)) with [c]: #2 is outer var 0 -> c; the rest are bound.
        let inner = {
            let b2 = s.mk_bvar(2);
            let b1 = s.mk_bvar(1);
            let b0 = s.mk_bvar(0);
            let x = s.mk_app(b2, b1);
            s.mk_app(x, b0)
        };
        let t = {
            let l = s.mk_lam(ty, inner);
            s.mk_lam(ty, l)
        };
        let new_inner = {
            let b1 = s.mk_bvar(1);
            let b0 = s.mk_bvar(0);
            let x = s.mk_app(c, b1);
            s.mk_app(x, b0)
        };
        let expect = {
            let l = s.mk_lam(ty, new_inner);
            s.mk_lam(ty, l)
        };
        assert_eq!(s.instantiate(t, &[c]), expect);
    }

    #[test]
    fn abstract_locals_basic_and_under_binder() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let l1 = s.mk_local(0, ty);
        let l2 = s.mk_local(1, ty);
        let t = s.mk_app(l1, l2);
        let b1 = s.mk_bvar(1);
        let b0 = s.mk_bvar(0);
        assert_eq!(s.abstract_locals(t, &[l1, l2]), s.mk_app(b1, b0));
        // l2 is locals[1] -> bvar 0; l1 -> bvar 1
        // under a binder: lam(ty, l1 #0) abstracting [l1] -> lam(ty, #1 #0)
        let b0b = s.mk_bvar(0);
        let body = s.mk_app(l1, b0b);
        let lam = s.mk_lam(ty, body);
        let b1x = s.mk_bvar(1);
        let expect_body = s.mk_app(b1x, b0b);
        let expect = s.mk_lam(ty, expect_body);
        assert_eq!(s.abstract_locals(lam, &[l1]), expect);
        // a term without the locals is unchanged
        let c = s.mk_const(1, 0);
        assert_eq!(s.abstract_locals(c, &[l1, l2]), c);
        // a term with only a deeper local is unchanged when abstracting shallower ones
        assert_eq!(s.abstract_locals(l2, &[l1]), l2);
    }

    #[test]
    fn instantiate_abstract_round_trip() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let l1 = s.mk_local(0, ty);
        let l2 = s.mk_local(1, ty);
        let t = {
            let b0 = s.mk_bvar(0);
            let b1 = s.mk_bvar(1);
            let inner = s.mk_app(b0, b1);
            let lam = s.mk_lam(ty, inner);
            s.mk_app(lam, b1)
        };
        let inst = s.instantiate(t, &[l1, l2]);
        let back = s.abstract_locals(inst, &[l1, l2]);
        assert_eq!(back, t);
    }

    #[test]
    fn beta_reduces_nested_lambdas_and_keeps_rest() {
        let mut s = Store::new();
        let z = s.mk_zero();
        let ty = s.mk_sort(z);
        let a = s.mk_const(1, 0);
        let b = s.mk_const(2, 0);
        let c = s.mk_const(3, 0);
        // f = lam ty. lam ty. (#1 #0)
        let f = {
            let b1 = s.mk_bvar(1);
            let b0 = s.mk_bvar(0);
            let body = s.mk_app(b1, b0);
            let inner = s.mk_lam(ty, body);
            s.mk_lam(ty, inner)
        };
        // beta(f, [a, b]) = a b
        assert_eq!(s.beta(f, &[a, b]), s.mk_app(a, b));
        // beta(f, [a]) = lam ty. a #0
        let b0 = s.mk_bvar(0);
        let expect = {
            let body = s.mk_app(a, b0);
            s.mk_lam(ty, body)
        };
        assert_eq!(s.beta(f, &[a]), expect);
        // beta(f, [a, b, c]) = (a b) c
        let ab = s.mk_app(a, b);
        assert_eq!(s.beta(f, &[a, b, c]), s.mk_app(ab, c));
        // non-lambda head: just application
        assert_eq!(s.beta(a, &[b, c]), s.mk_app_n(a, &[b, c]));
    }

    #[test]
    fn unfold_app_order_and_helpers() {
        let mut s = Store::new();
        let f = s.mk_const(1, 0);
        let a = s.mk_const(2, 0);
        let b = s.mk_const(3, 0);
        let c = s.mk_const(4, 0);
        let t = s.mk_app_n(f, &[a, b, c]);
        assert_eq!(s.app_fn(t), f);
        assert_eq!(s.app_num_args(t), 3);
        assert_eq!(s.app_num_args(f), 0);
        let mut args = vec![999];
        let h = s.unfold_app(t, &mut args);
        assert_eq!(h, f);
        assert_eq!(args, vec![999, a, b, c]);
        let mut args2 = Vec::new();
        assert_eq!(s.unfold_app(f, &mut args2), f);
        assert!(args2.is_empty());
        assert_eq!(s.mk_app_n(f, &[]), f);
    }

    #[test]
    fn subst_params_sorts_consts_locals_and_binders() {
        let mut s = Store::new();
        let u = s.mk_param(1);
        let z = s.mk_zero();
        let one = s.mk_level_nat(1);
        let lv_u = s.mk_levels(&[u]);
        let lv_z = s.mk_levels(&[z]);
        // sort u
        let su = s.mk_sort(u);
        assert_eq!(s.subst_params(su, &[1], lv_z), s.mk_sort(z));
        // const c.{u}
        let cu = s.mk_const(5, lv_u);
        assert_eq!(s.subst_params(cu, &[1], lv_z), s.mk_const(5, lv_z));
        // lam (sort u). #0 under a binder, with a param-free part untouched
        let b0 = s.mk_bvar(0);
        let lam = s.mk_lam(su, b0);
        let sz = s.mk_sort(z);
        let lam_expect = s.mk_lam(sz, b0);
        assert_eq!(s.subst_params(lam, &[1], lv_z), lam_expect);
        // substitution to a successor
        let lv_one = s.mk_levels(&[one]);
        assert_eq!(s.subst_params(su, &[1], lv_one), s.mk_sort(one));
        // no params: identity
        let c0 = s.mk_const(6, 0);
        assert_eq!(s.subst_params(c0, &[], 0), c0);
        // a local whose type mentions u gets a substituted type
        let lu = s.mk_local(0, su);
        let szz = s.mk_sort(z);
        let lz = s.mk_local(0, szz);
        assert_eq!(s.subst_params(lu, &[1], lv_z), lz);
        // simultaneous substitution of two params
        let v = s.mk_param(2);
        let sv = s.mk_sort(v);
        let pair = s.mk_app(su, sv);
        let lv_zv = s.mk_levels(&[z, one]);
        let res = s.subst_params(pair, &[1, 2], lv_zv);
        let (sz2, so) = (s.mk_sort(z), s.mk_sort(one));
        let expect = s.mk_app(sz2, so);
        assert_eq!(res, expect);
    }

    #[test]
    fn dag_with_huge_tree_size_is_fast() {
        let mut s = Store::new();
        // x_40 = x_39 x_39 ... tree size 2^40 with 41 distinct nodes.
        let mut x = s.mk_bvar(0);
        for _ in 0..40 {
            x = s.mk_app(x, x);
        }
        let c = s.mk_const(1, 0);
        let mut expect = c;
        for _ in 0..40 {
            expect = s.mk_app(expect, expect);
        }
        assert_eq!(s.instantiate(x, &[c]), expect);
        // abstraction on the same shape
        let zz = s.mk_zero();
        let szz = s.mk_sort(zz);
        let l = s.mk_local(0, szz);
        let mut y = l;
        for _ in 0..40 {
            y = s.mk_app(y, y);
        }
        let mut expect_b = s.mk_bvar(0);
        for _ in 0..40 {
            expect_b = s.mk_app(expect_b, expect_b);
        }
        assert_eq!(s.abstract_locals(y, &[l]), expect_b);
        // subst_params on the same shape with params
        let u = s.mk_param(1);
        let mut w = s.mk_sort(u);
        for _ in 0..40 {
            w = s.mk_app(w, w);
        }
        let z = s.mk_zero();
        let lv = s.mk_levels(&[z]);
        let mut expect_w = s.mk_sort(z);
        for _ in 0..40 {
            expect_w = s.mk_app(expect_w, expect_w);
        }
        assert_eq!(s.subst_params(w, &[1], lv), expect_w);
    }

    #[test]
    fn long_application_spine_does_not_recurse() {
        with_big_stack(|| {
            let mut s = Store::new();
            let n = 100_000u32;
            let f = s.mk_bvar(0);
            let args: Vec<TermId> = (0..n).map(|i| s.mk_bvar(i)).collect();
            let t = s.mk_app_n(f, &args);
            assert_eq!(s.app_num_args(t), n as usize);
            assert_eq!(s.lbr(t), n);
            let c = s.mk_const(1, 0);
            let r = s.instantiate(t, &[c]);
            assert_eq!(s.app_num_args(r), n as usize);
            assert_eq!(s.app_fn(r), c);
            let mut out = Vec::new();
            let h = s.unfold_app(r, &mut out);
            assert_eq!(h, c);
            assert_eq!(out.len(), n as usize);
            // args[0] = #0 is replaced by c; args[i] = #i becomes #(i-1)
            assert_eq!(out[0], c);
            assert_eq!(out[(n - 1) as usize], s.mk_bvar(n - 2));
            // abstraction over a spine of locals
            let zz = s.mk_zero();
            let ty = s.mk_sort(zz);
            let l = s.mk_local(0, ty);
            let lspine: Vec<TermId> = (0..n).map(|_| l).collect();
            let lt = s.mk_app_n(l, &lspine);
            let abs = s.abstract_locals(lt, &[l]);
            assert_eq!(s.lbr(abs), 1);
            assert_eq!(s.app_num_args(abs), n as usize);
            // subst on a spine with parameters
            let u = s.mk_param(1);
            let su = s.mk_sort(u);
            let sargs: Vec<TermId> = (0..n).map(|_| su).collect();
            let st = s.mk_app_n(f, &sargs);
            let zz = s.mk_zero();
            let lv = s.mk_levels(&[zz]);
            let sr = s.subst_params(st, &[1], lv);
            assert_eq!(s.app_num_args(sr), n as usize);
        });
    }

    #[test]
    fn clear_resets_store() {
        let mut s = Store::new();
        let _ = s.mk_bvar(3);
        let _ = s.mk_nat_u64(9);
        assert!(s.num_terms() > 0);
        s.clear();
        assert_eq!(s.num_terms(), 0);
        let b = s.mk_bvar(3);
        assert_eq!(s.num_terms(), 1);
        assert_eq!(s.get(b), Term::BVar(3));
        assert_eq!(s.mk_levels(&[]), 0);
    }

    #[test]
    fn growth_keeps_identities() {
        let mut s = Store::new();
        let ids: Vec<TermId> = (0..20_000u32).map(|i| s.mk_bvar(i)).collect();
        for (i, &id) in ids.iter().enumerate() {
            assert_eq!(s.mk_bvar(i as u32), id);
        }
        let mut lv = Vec::new();
        for i in 0..5_000u32 {
            let l = s.mk_param(i + 1);
            lv.push(l);
        }
        for w in lv.windows(3) {
            let a = s.mk_levels(w);
            assert_eq!(a, s.mk_levels(w));
        }
    }

}

//! Shared environment data types. See docs/DESIGN.md section 3.
//!
//! `RawEnv` is the file as read: canonical names, levels, expressions and
//! declarations, all addressed by dense ids. `Env` adds the constant table
//! (indexed by `NameId`) and the resolved builtin names.

use std::collections::HashMap;

use crate::bignat::BigNat;

/// Canonical name id. Equal names have equal ids. 0 is the anonymous name.
pub type NameId = u32;
/// Index into `RawEnv::exprs`.
pub type RawExpr = u32;
/// Index into `RawEnv::levels`. 0 is `zero`.
pub type RawLevel = u32;

/// One interned name. A name's prefix always has a smaller id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameNode {
    Anon,
    Str(NameId, Box<str>),
    Num(NameId, u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RawLevelNode {
    Zero,
    Succ(RawLevel),
    Max(RawLevel, RawLevel),
    IMax(RawLevel, RawLevel),
    Param(NameId),
}

/// Expression kind. `mdata` is transparent and never appears as a tag.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RawTag {
    BVar,
    Sort,
    Const,
    App,
    Lam,
    Pi,
    Let,
    Proj,
    Nat,
    Str,
}

/// A raw expression node (16 bytes). Field meaning by tag:
/// * `BVar`: a = index (saturated at u32::MAX)
/// * `Sort`: a = level
/// * `Const`: a = name, b = offset into `RawEnv::const_levels`, c = number of levels
/// * `App`: a = function, b = argument
/// * `Lam` / `Pi`: a = binder type, b = body (binder name and info are dropped)
/// * `Let`: a = type, b = value, c = body (`nondep` is dropped)
/// * `Proj`: a = structure type name, b = field index (saturated), c = struct expression
/// * `Nat`: a = index into `RawEnv::nats`
/// * `Str`: a = index into `RawEnv::strs`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawNode {
    pub tag: RawTag,
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

/// Declaration header kinds. Constant data lives in `Env::consts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Axiom { name: NameId },
    Def { name: NameId },
    Thm { name: NameId },
    Opaque { name: NameId },
    Quot { name: NameId },
    Inductive { types: Vec<NameId>, ctors: Vec<NameId>, recs: Vec<NameId> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Safety {
    Unsafe,
    Safe,
    Partial,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductInfo {
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u32,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CtorInfo {
    pub induct: NameId,
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecRule {
    pub ctor: NameId,
    pub nfields: u32,
    pub rhs: RawExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecInfo {
    pub all: Vec<NameId>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstKind {
    Axiom,
    Def { value: RawExpr, hints: Hints, safety: Safety, all: Vec<NameId> },
    Thm { value: RawExpr, all: Vec<NameId> },
    Opaque { value: RawExpr, all: Vec<NameId> },
    Quot(QuotKind),
    Induct(InductInfo),
    Ctor(CtorInfo),
    Rec(RecInfo),
}

/// Data of one constant. `pos` is the position of the declaration that
/// introduced it. All constants of an inductive block share that position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstInfo {
    pub pos: u32,
    pub level_params: Vec<NameId>,
    pub ty: RawExpr,
    pub kind: ConstKind,
    /// `isUnsafe`, or a def whose safety is `unsafe` or `partial`.
    pub is_unsafe: bool,
}

/// The file as read. Index 0 of `names` and `levels` is predefined.
#[derive(Debug)]
pub struct RawEnv {
    pub names: Vec<NameNode>,
    pub levels: Vec<RawLevelNode>,
    pub exprs: Vec<RawNode>,
    pub const_levels: Vec<RawLevel>,
    pub nats: Vec<BigNat>,
    pub strs: Vec<String>,
    /// One entry per declaration line, in file order. The index is the position.
    pub decls: Vec<Decl>,
    /// Name hash -> most recently interned name with that hash.
    name_head: HashMap<u64, NameId>,
    /// Per name: the next older name with the same hash (`NONE` ends the chain).
    name_next: Vec<NameId>,
}

const NONE: NameId = u32::MAX;

fn name_hash(prefix: NameId, kind: u8, payload: &[u8]) -> u64 {
    let p = prefix.to_le_bytes();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in p.iter().chain(std::slice::from_ref(&kind)).chain(payload) {
        h = (h ^ b as u64).wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

impl RawEnv {
    pub fn new() -> Self {
        RawEnv {
            names: vec![NameNode::Anon],
            levels: vec![RawLevelNode::Zero],
            exprs: Vec::new(),
            const_levels: Vec::new(),
            nats: Vec::new(),
            strs: Vec::new(),
            decls: Vec::new(),
            name_head: HashMap::new(),
            name_next: vec![NONE],
        }
    }

    /// Dot-separated rendering of a name, e.g. `Nat.succ`. The anonymous name renders as `[anonymous]`.
    pub fn name_to_string(&self, id: NameId) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur = id;
        loop {
            match self.names.get(cur as usize) {
                Some(NameNode::Str(p, s)) => {
                    parts.push(s.to_string());
                    cur = *p;
                }
                Some(NameNode::Num(p, n)) => {
                    parts.push(n.to_string());
                    cur = *p;
                }
                _ => break,
            }
        }
        if parts.is_empty() {
            return "[anonymous]".to_string();
        }
        parts.reverse();
        parts.join(".")
    }

    /// Looks up an all-string name such as `["Nat", "succ"]` without inserting it.
    pub fn find_name(&self, comps: &[&str]) -> Option<NameId> {
        let mut cur: NameId = 0;
        for c in comps {
            cur = self.find_str(cur, c)?;
        }
        Some(cur)
    }

    fn find_str(&self, prefix: NameId, comp: &str) -> Option<NameId> {
        let h = name_hash(prefix, 0, comp.as_bytes());
        let mut cur = *self.name_head.get(&h)?;
        while cur != NONE {
            if let Some(NameNode::Str(p, s)) = self.names.get(cur as usize) {
                if *p == prefix && &**s == comp {
                    return Some(cur);
                }
            }
            cur = *self.name_next.get(cur as usize)?;
        }
        None
    }

    fn find_num(&self, prefix: NameId, n: u64) -> Option<NameId> {
        let h = name_hash(prefix, 1, &n.to_le_bytes());
        let mut cur = *self.name_head.get(&h)?;
        while cur != NONE {
            if let Some(NameNode::Num(p, m)) = self.names.get(cur as usize) {
                if *p == prefix && *m == n {
                    return Some(cur);
                }
            }
            cur = *self.name_next.get(cur as usize)?;
        }
        None
    }

    /// Interns `prefix.comp`. Returns the id and whether it was newly created.
    pub(crate) fn intern_str(&mut self, prefix: NameId, comp: &str) -> (NameId, bool) {
        if let Some(id) = self.find_str(prefix, comp) {
            return (id, false);
        }
        let h = name_hash(prefix, 0, comp.as_bytes());
        self.push_name(h, NameNode::Str(prefix, comp.into()))
    }

    /// Interns `prefix.n`. Returns the id and whether it was newly created.
    pub(crate) fn intern_num(&mut self, prefix: NameId, n: u64) -> (NameId, bool) {
        if let Some(id) = self.find_num(prefix, n) {
            return (id, false);
        }
        let h = name_hash(prefix, 1, &n.to_le_bytes());
        self.push_name(h, NameNode::Num(prefix, n))
    }

    fn push_name(&mut self, h: u64, node: NameNode) -> (NameId, bool) {
        let id = self.names.len() as NameId;
        self.names.push(node);
        let next = self.name_head.insert(h, id).unwrap_or(NONE);
        self.name_next.push(next);
        (id, true)
    }
}

impl Default for RawEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// Builtin names the checker needs. `None` when the file does not declare them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Builtins {
    pub nat_ty: Option<NameId>,
    pub nat_zero: Option<NameId>,
    pub nat_succ: Option<NameId>,
    pub nat_add: Option<NameId>,
    pub nat_sub: Option<NameId>,
    pub nat_mul: Option<NameId>,
    pub nat_div: Option<NameId>,
    pub nat_mod: Option<NameId>,
    pub nat_gcd: Option<NameId>,
    pub nat_beq: Option<NameId>,
    pub nat_ble: Option<NameId>,
    pub nat_land: Option<NameId>,
    pub nat_lor: Option<NameId>,
    pub nat_xor: Option<NameId>,
    pub nat_shift_left: Option<NameId>,
    pub nat_shift_right: Option<NameId>,
    pub nat_pow: Option<NameId>,
    pub nat_log2: Option<NameId>,
    pub bool_ty: Option<NameId>,
    pub bool_true: Option<NameId>,
    pub bool_false: Option<NameId>,
    pub string_ty: Option<NameId>,
    pub string_of_list: Option<NameId>,
    pub char_ty: Option<NameId>,
    pub char_of_nat: Option<NameId>,
    pub list_ty: Option<NameId>,
    pub list_nil: Option<NameId>,
    pub list_cons: Option<NameId>,
    pub quot_ty: Option<NameId>,
    pub quot_mk: Option<NameId>,
    pub quot_lift: Option<NameId>,
    pub quot_ind: Option<NameId>,
    pub eq_ty: Option<NameId>,
    pub eq_refl: Option<NameId>,
    pub eager_reduce: Option<NameId>,
}

impl Builtins {
    /// Resolves every builtin name in `raw`.
    pub fn resolve(raw: &RawEnv) -> Self {
        let f = |comps: &[&str]| raw.find_name(comps);
        Builtins {
            nat_ty: f(&["Nat"]),
            nat_zero: f(&["Nat", "zero"]),
            nat_succ: f(&["Nat", "succ"]),
            nat_add: f(&["Nat", "add"]),
            nat_sub: f(&["Nat", "sub"]),
            nat_mul: f(&["Nat", "mul"]),
            nat_div: f(&["Nat", "div"]),
            nat_mod: f(&["Nat", "mod"]),
            nat_gcd: f(&["Nat", "gcd"]),
            nat_beq: f(&["Nat", "beq"]),
            nat_ble: f(&["Nat", "ble"]),
            nat_land: f(&["Nat", "land"]),
            nat_lor: f(&["Nat", "lor"]),
            nat_xor: f(&["Nat", "xor"]),
            nat_shift_left: f(&["Nat", "shiftLeft"]),
            nat_shift_right: f(&["Nat", "shiftRight"]),
            nat_pow: f(&["Nat", "pow"]),
            nat_log2: f(&["Nat", "log2"]),
            bool_ty: f(&["Bool"]),
            bool_true: f(&["Bool", "true"]),
            bool_false: f(&["Bool", "false"]),
            string_ty: f(&["String"]),
            string_of_list: f(&["String", "ofList"]),
            char_ty: f(&["Char"]),
            char_of_nat: f(&["Char", "ofNat"]),
            list_ty: f(&["List"]),
            list_nil: f(&["List", "nil"]),
            list_cons: f(&["List", "cons"]),
            quot_ty: f(&["Quot"]),
            quot_mk: f(&["Quot", "mk"]),
            quot_lift: f(&["Quot", "lift"]),
            quot_ind: f(&["Quot", "ind"]),
            eq_ty: f(&["Eq"]),
            eq_refl: f(&["Eq", "refl"]),
            eager_reduce: f(&["eagerReduce"]),
        }
    }
}

/// A loaded export: the raw file, the constant table and the builtins.
#[derive(Debug)]
pub struct Env {
    pub raw: RawEnv,
    /// Indexed by `NameId`. `None` for names that are not declared constants.
    pub consts: Vec<Option<ConstInfo>>,
    pub builtins: Builtins,
}

impl Env {
    pub fn get(&self, name: NameId) -> Option<&ConstInfo> {
        self.consts.get(name as usize).and_then(|c| c.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_interning_is_canonical() {
        let mut raw = RawEnv::new();
        let (nat, fresh) = raw.intern_str(0, "Nat");
        assert!(fresh);
        let (nat2, fresh2) = raw.intern_str(0, "Nat");
        assert_eq!((nat, false), (nat2, fresh2));
        let (succ, _) = raw.intern_str(nat, "succ");
        let (n1, _) = raw.intern_num(succ, 1);
        let (n2, _) = raw.intern_num(succ, 1);
        assert_eq!(n1, n2);
        assert_eq!(raw.name_to_string(succ), "Nat.succ");
        assert_eq!(raw.name_to_string(n1), "Nat.succ.1");
        assert_eq!(raw.name_to_string(0), "[anonymous]");
        assert_eq!(raw.find_name(&["Nat", "succ"]), Some(succ));
        assert_eq!(raw.find_name(&["Nat", "pred"]), None);
        assert_eq!(raw.find_name(&[]), Some(0));
        assert_eq!(raw.names.len(), 4);
    }

    #[test]
    fn builtins_resolve() {
        let mut raw = RawEnv::new();
        let (nat, _) = raw.intern_str(0, "Nat");
        let (zero, _) = raw.intern_str(nat, "zero");
        let b = Builtins::resolve(&raw);
        assert_eq!(b.nat_ty, Some(nat));
        assert_eq!(b.nat_zero, Some(zero));
        assert_eq!(b.nat_add, None);
    }
}

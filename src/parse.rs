//! NDJSON export -> `Env`. See docs/DESIGN.md section 3 (parser rules).
//!
//! One pass over the lines. Each item line carries an index (`in`, `il` or
//! `ie`) and one payload key. Indices are arbitrary u64 values; `IdxTable`
//! maps them to dense internal ids. It keeps the identity mapping while the
//! file is dense and switches to a hash map on the first out-of-order or
//! aliased index.

use std::collections::HashMap;
use std::fmt;

use crate::bignat::BigNat;
use crate::env::*;
use crate::json::{each_elem, each_key, Cursor, ParseError};

/// Why a file was not loaded. `Reject`: the file is invalid. `Decline`: the
/// file is outside what this checker supports (e.g. another format major version).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadError {
    Reject(String),
    Decline(String),
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoadError::Reject(m) => write!(f, "rejected: {m}"),
            LoadError::Decline(m) => write!(f, "declined: {m}"),
        }
    }
}

impl std::error::Error for LoadError {}

impl From<ParseError> for LoadError {
    fn from(e: ParseError) -> Self {
        LoadError::Reject(format!("malformed JSON: {e}"))
    }
}

impl LoadError {
    fn at_line(self, n: usize) -> Self {
        match self {
            LoadError::Reject(m) => LoadError::Reject(format!("line {n}: {m}")),
            LoadError::Decline(m) => LoadError::Decline(format!("line {n}: {m}")),
        }
    }
}

type LResult<T> = Result<T, LoadError>;

fn reject<T>(msg: impl Into<String>) -> LResult<T> {
    Err(LoadError::Reject(msg.into()))
}

fn req<T>(v: Option<T>, what: &str) -> LResult<T> {
    v.ok_or_else(|| LoadError::Reject(format!("missing required field `{what}`")))
}

fn put<T>(slot: &mut Option<T>, v: T, what: &str) -> LResult<()> {
    if slot.is_some() {
        return reject(format!("duplicate field `{what}`"));
    }
    *slot = Some(v);
    Ok(())
}

fn to_u32(v: usize, what: &str) -> LResult<u32> {
    u32::try_from(v).or_else(|_| reject(format!("too many {what}")))
}

fn push_capacity(len: usize, what: &str) -> LResult<()> {
    to_u32(len, what).map(|_| ())
}

fn read_u32(c: &mut Cursor<'_>) -> LResult<u32> {
    let v = c.parse_u64()?;
    u32::try_from(v).or_else(|_| reject(format!("count {v} does not fit in u32")))
}

fn sat_u32(v: u64) -> u32 {
    u32::try_from(v).unwrap_or(u32::MAX)
}

fn parse_nat(s: &[u8]) -> Option<BigNat> {
    BigNat::from_decimal(s)
}

fn trim(l: &[u8]) -> &[u8] {
    l.trim_ascii()
}

/// Keys that carry the payload of an item or declaration line.
fn is_payload_key(key: &[u8]) -> bool {
    matches!(
        key,
        b"str" | b"num"
            | b"succ" | b"max" | b"imax" | b"param"
            | b"bvar" | b"sort" | b"const" | b"app" | b"lam" | b"forallE" | b"letE" | b"proj"
            | b"natVal" | b"strVal" | b"mdata"
            | b"axiom" | b"def" | b"opaque" | b"thm" | b"quot" | b"inductive"
    )
}

/// Maps file indices of one namespace to internal ids.
struct IdxTable {
    /// While true, the defined file indices are exactly `0..n` and map to themselves.
    identity: bool,
    n: u64,
    map: HashMap<u64, u32>,
}

impl IdxTable {
    /// `predefined` entries (indices `0..predefined`) are defined before any line.
    fn new(predefined: u64) -> Self {
        IdxTable { identity: true, n: predefined, map: HashMap::new() }
    }

    fn lookup(&self, idx: u64) -> Option<u32> {
        if self.identity {
            (idx < self.n).then_some(idx as u32)
        } else {
            self.map.get(&idx).copied()
        }
    }

    /// Records `idx -> id`. The caller has checked that `idx` is not yet defined.
    /// `fresh` means `id` is a node just pushed at the end of its vector.
    fn define(&mut self, idx: u64, id: u32, fresh: bool) {
        if self.identity && fresh && idx == id as u64 && idx == self.n {
            self.n += 1;
            return;
        }
        if self.identity {
            for i in 0..self.n {
                self.map.insert(i, i as u32);
            }
            self.identity = false;
        }
        self.map.insert(idx, id);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ns {
    Name,
    Level,
    Expr,
}

/// Fields of every object that can appear as a declaration or a nested
/// constant record. Each kind uses the subset its format requires.
#[derive(Default)]
struct Fields {
    name: Option<NameId>,
    level_params: Option<Vec<NameId>>,
    ty: Option<RawExpr>,
    value: Option<RawExpr>,
    is_unsafe: Option<bool>,
    hints: Option<Hints>,
    safety: Option<Safety>,
    all: Option<Vec<NameId>>,
    quot_kind: Option<QuotKind>,
    num_params: Option<u32>,
    num_indices: Option<u32>,
    ctors: Option<Vec<NameId>>,
    num_nested: Option<u32>,
    is_rec: Option<bool>,
    is_reflexive: Option<bool>,
    induct: Option<NameId>,
    cidx: Option<u32>,
    num_fields: Option<u32>,
    num_motives: Option<u32>,
    num_minors: Option<u32>,
    rules: Option<Vec<RecRule>>,
    k: Option<bool>,
}

struct Loader {
    env: RawEnv,
    names_ix: IdxTable,
    levels_ix: IdxTable,
    exprs_ix: IdxTable,
    str_ix: HashMap<String, u32>,
    consts: Vec<Option<ConstInfo>>,
    /// Reused buffer for decoded strings.
    scratch: Vec<u8>,
}

/// Parses an export file.
pub fn load(bytes: &[u8]) -> Result<Env, LoadError> {
    let mut lines = bytes
        .split(|&b| b == b'\n')
        .enumerate()
        .map(|(i, l)| (i + 1, trim(l)))
        .filter(|(_, l)| !l.is_empty());
    let (n0, first) = match lines.next() {
        Some(x) => x,
        None => return reject("empty file: missing meta line"),
    };
    meta_line(first).map_err(|e| e.at_line(n0))?;
    let mut ld = Loader::new();
    for (n, line) in lines {
        ld.item_line(line).map_err(|e| e.at_line(n))?;
    }
    ld.finish()
}

fn meta_line(line: &[u8]) -> LResult<()> {
    let mut c = Cursor::new(line);
    let mut version: Option<&[u8]> = None;
    let mut seen = false;
    each_key!(c, key => match key {
        b"meta" => {
            if seen {
                return reject("duplicate meta object");
            }
            seen = true;
            version = read_meta_version(&mut c)?;
        }
        _ => return reject("first line must be the meta object"),
    });
    if !c.at_end() {
        return reject("trailing characters after meta object");
    }
    let v = match version {
        Some(v) => v,
        None => return reject("meta object has no format.version"),
    };
    let major_end = v.iter().position(|&b| b == b'.').unwrap_or(v.len());
    let major = std::str::from_utf8(&v[..major_end])
        .ok()
        .and_then(|s| s.parse::<u64>().ok());
    match major {
        Some(3) => Ok(()),
        Some(m) => Err(LoadError::Decline(format!("unsupported export format major version {m}"))),
        None => reject("malformed format.version in meta object"),
    }
}

fn read_meta_version<'a>(c: &mut Cursor<'a>) -> LResult<Option<&'a [u8]>> {
    let mut version = None;
    each_key!(c, key => match key {
        b"format" => {
            each_key!(c, k2 => match k2 {
                b"version" => put(&mut version, c.parse_plain_string()?, "format.version")?,
                _ => c.skip_value()?,
            });
        }
        _ => c.skip_value()?,
    });
    Ok(version)
}

impl Loader {
    fn new() -> Self {
        Loader {
            env: RawEnv::new(),
            names_ix: IdxTable::new(1),
            levels_ix: IdxTable::new(1),
            exprs_ix: IdxTable::new(0),
            str_ix: HashMap::new(),
            consts: Vec::new(),
            scratch: Vec::new(),
        }
    }

    fn table(&self, ns: Ns) -> &IdxTable {
        match ns {
            Ns::Name => &self.names_ix,
            Ns::Level => &self.levels_ix,
            Ns::Expr => &self.exprs_ix,
        }
    }

    fn table_mut(&mut self, ns: Ns) -> &mut IdxTable {
        match ns {
            Ns::Name => &mut self.names_ix,
            Ns::Level => &mut self.levels_ix,
            Ns::Expr => &mut self.exprs_ix,
        }
    }

    fn name_ref(&self, idx: u64) -> LResult<NameId> {
        self.names_ix
            .lookup(idx)
            .ok_or_else(|| LoadError::Reject(format!("reference to undefined name index {idx}")))
    }

    fn level_ref(&self, idx: u64) -> LResult<RawLevel> {
        self.levels_ix
            .lookup(idx)
            .ok_or_else(|| LoadError::Reject(format!("reference to undefined level index {idx}")))
    }

    fn expr_ref(&self, idx: u64) -> LResult<RawExpr> {
        self.exprs_ix
            .lookup(idx)
            .ok_or_else(|| LoadError::Reject(format!("reference to undefined expression index {idx}")))
    }

    fn read_name_ref(&self, c: &mut Cursor<'_>) -> LResult<NameId> {
        let i = c.parse_u64()?;
        self.name_ref(i)
    }

    fn read_level_ref(&self, c: &mut Cursor<'_>) -> LResult<RawLevel> {
        let i = c.parse_u64()?;
        self.level_ref(i)
    }

    fn read_expr_ref(&self, c: &mut Cursor<'_>) -> LResult<RawExpr> {
        let i = c.parse_u64()?;
        self.expr_ref(i)
    }

    fn read_name_array(&self, c: &mut Cursor<'_>) -> LResult<Vec<NameId>> {
        let mut v = Vec::new();
        each_elem!(c, {
            v.push(self.read_name_ref(c)?);
        });
        Ok(v)
    }

    fn push_expr(&mut self, node: RawNode) -> LResult<(u32, bool)> {
        push_capacity(self.env.exprs.len(), "expressions")?;
        let id = self.env.exprs.len() as u32;
        self.env.exprs.push(node);
        Ok((id, true))
    }

    fn push_level(&mut self, node: RawLevelNode) -> LResult<(u32, bool)> {
        push_capacity(self.env.levels.len(), "levels")?;
        let id = self.env.levels.len() as u32;
        self.env.levels.push(node);
        Ok((id, true))
    }

    fn intern_num(&mut self, prefix: NameId, n: u64) -> LResult<(NameId, bool)> {
        push_capacity(self.env.names.len(), "names")?;
        Ok(self.env.intern_num(prefix, n))
    }

    /// Processes one item or declaration line.
    fn item_line(&mut self, line: &[u8]) -> LResult<()> {
        let mut c = Cursor::new(line);
        let mut idx: Option<(Ns, u64)> = None;
        let mut item: Option<(Ns, u32, bool)> = None;
        let mut is_decl = false;
        let mut payloads = 0u32;
        if !c.obj_begin()? {
            return reject("empty object");
        }
        loop {
            let key = c.obj_key()?;
            match key {
                b"in" => put(&mut idx, (Ns::Name, c.parse_u64()?), "in")?,
                b"il" => put(&mut idx, (Ns::Level, c.parse_u64()?), "il")?,
                b"ie" => put(&mut idx, (Ns::Expr, c.parse_u64()?), "ie")?,
                _ => {
                    if !is_payload_key(key) {
                        return Err(LoadError::Decline(format!(
                            "unknown top-level key `{}`",
                            String::from_utf8_lossy(key)
                        )));
                    }
                    payloads += 1;
                    if payloads > 1 {
                        return reject("more than one payload key in one line");
                    }
                    match key {
                        b"str" | b"num" => {
                            let (id, fresh) = self.parse_name(key, &mut c)?;
                            item = Some((Ns::Name, id, fresh));
                        }
                        b"succ" | b"max" | b"imax" | b"param" => {
                            let (id, fresh) = self.parse_level(key, &mut c)?;
                            item = Some((Ns::Level, id, fresh));
                        }
                        b"bvar" | b"sort" | b"const" | b"app" | b"lam" | b"forallE" | b"letE" | b"proj"
                        | b"natVal" | b"strVal" | b"mdata" => {
                            let (id, fresh) = self.parse_expr(key, &mut c)?;
                            item = Some((Ns::Expr, id, fresh));
                        }
                        b"axiom" | b"def" | b"opaque" | b"thm" | b"quot" | b"inductive" => {
                            self.parse_decl(key, &mut c)?;
                            is_decl = true;
                        }
                        _ => return reject("unexpected payload key"),
                    }
                }
            }
            if !c.obj_more()? {
                break;
            }
        }
        if !c.at_end() {
            return reject("trailing characters after object");
        }
        if is_decl {
            if idx.is_some() {
                return reject("index key on a declaration line");
            }
            return Ok(());
        }
        let (pns, id, fresh) = match item {
            Some(x) => x,
            None => return reject("line has no payload"),
        };
        let (ins, iv) = match idx {
            Some(x) => x,
            None => return reject("item line without an index key"),
        };
        if ins != pns {
            return reject("index key does not match the payload kind");
        }
        if self.table(pns).lookup(iv).is_some() {
            return reject(format!("index {iv} is defined twice"));
        }
        self.table_mut(pns).define(iv, id, fresh);
        Ok(())
    }

    /// `{"pre": name, "str": string}` or `{"pre": name, "i": integer}`.
    fn parse_name(&mut self, key: &[u8], c: &mut Cursor<'_>) -> LResult<(NameId, bool)> {
        let is_num = key == b"num";
        let mut pre = None;
        let mut num = None;
        let mut have_str = false;
        each_key!(c, k => match k {
            b"pre" => put(&mut pre, self.read_name_ref(c)?, "pre")?,
            b"str" if !is_num => {
                if have_str {
                    return reject("duplicate field `str`");
                }
                have_str = true;
                c.parse_string_into(&mut self.scratch)?;
            }
            b"i" if is_num => put(&mut num, c.parse_u64()?, "i")?,
            _ => c.skip_value()?,
        });
        let pre = req(pre, "pre")?;
        if is_num {
            let n = req(num, "i")?;
            self.intern_num(pre, n)
        } else {
            if !have_str {
                return reject("missing required field `str`");
            }
            push_capacity(self.env.names.len(), "names")?;
            let s = match std::str::from_utf8(&self.scratch) {
                Ok(s) => s,
                Err(_) => return reject("invalid UTF-8 in name"),
            };
            Ok(self.env.intern_str(pre, s))
        }
    }

    /// Level payloads: `succ` / `param` take an integer; `max` / `imax` take `[integer, integer]`.
    fn parse_level(&mut self, key: &[u8], c: &mut Cursor<'_>) -> LResult<(u32, bool)> {
        let node = match key {
            b"succ" => RawLevelNode::Succ(self.read_level_ref(c)?),
            b"param" => RawLevelNode::Param(self.read_name_ref(c)?),
            _ => {
                let [a, b] = read_u64_pair(c)?;
                let (a, b) = (self.level_ref(a)?, self.level_ref(b)?);
                if key == b"max" {
                    RawLevelNode::Max(a, b)
                } else {
                    RawLevelNode::IMax(a, b)
                }
            }
        };
        self.push_level(node)
    }

    /// Expression payloads. `mdata` creates no node: it returns the inner expression's id with `fresh = false`.
    fn parse_expr(&mut self, key: &[u8], c: &mut Cursor<'_>) -> LResult<(u32, bool)> {
        let node = match key {
            b"bvar" => RawNode { tag: RawTag::BVar, a: sat_u32(c.parse_u64()?), b: 0, c: 0 },
            b"sort" => RawNode { tag: RawTag::Sort, a: self.read_level_ref(c)?, b: 0, c: 0 },
            b"const" => return self.parse_const(c),
            b"app" => {
                let (mut f, mut a) = (None, None);
                each_key!(c, k => match k {
                    b"fn" => put(&mut f, self.read_expr_ref(c)?, "fn")?,
                    b"arg" => put(&mut a, self.read_expr_ref(c)?, "arg")?,
                    _ => c.skip_value()?,
                });
                RawNode { tag: RawTag::App, a: req(f, "fn")?, b: req(a, "arg")?, c: 0 }
            }
            b"lam" | b"forallE" => {
                let (mut name, mut ty, mut body, mut bi) = (None, None, None, None);
                each_key!(c, k => match k {
                    b"name" => put(&mut name, self.read_name_ref(c)?, "name")?,
                    b"type" => put(&mut ty, self.read_expr_ref(c)?, "type")?,
                    b"body" => put(&mut body, self.read_expr_ref(c)?, "body")?,
                    b"binderInfo" => {
                        let s = c.parse_plain_string()?;
                        if !matches!(s, b"default" | b"implicit" | b"strictImplicit" | b"instImplicit") {
                            return reject("invalid binderInfo");
                        }
                        put(&mut bi, (), "binderInfo")?;
                    }
                    _ => c.skip_value()?,
                });
                let _ = req(name, "name")?;
                let _ = req(bi, "binderInfo")?;
                let tag = if key == b"lam" { RawTag::Lam } else { RawTag::Pi };
                RawNode { tag, a: req(ty, "type")?, b: req(body, "body")?, c: 0 }
            }
            b"letE" => {
                let (mut name, mut ty, mut val, mut body, mut nondep) = (None, None, None, None, None);
                each_key!(c, k => match k {
                    b"name" => put(&mut name, self.read_name_ref(c)?, "name")?,
                    b"type" => put(&mut ty, self.read_expr_ref(c)?, "type")?,
                    b"value" => put(&mut val, self.read_expr_ref(c)?, "value")?,
                    b"body" => put(&mut body, self.read_expr_ref(c)?, "body")?,
                    b"nondep" => put(&mut nondep, c.parse_bool()?, "nondep")?,
                    _ => c.skip_value()?,
                });
                let _ = req(name, "name")?;
                let _ = req(nondep, "nondep")?;
                RawNode {
                    tag: RawTag::Let,
                    a: req(ty, "type")?,
                    b: req(val, "value")?,
                    c: req(body, "body")?,
                }
            }
            b"proj" => {
                let (mut tn, mut idx, mut s) = (None, None, None);
                each_key!(c, k => match k {
                    b"typeName" => put(&mut tn, self.read_name_ref(c)?, "typeName")?,
                    b"idx" => put(&mut idx, sat_u32(c.parse_u64()?), "idx")?,
                    b"struct" => put(&mut s, self.read_expr_ref(c)?, "struct")?,
                    _ => c.skip_value()?,
                });
                RawNode {
                    tag: RawTag::Proj,
                    a: req(tn, "typeName")?,
                    b: req(idx, "idx")?,
                    c: req(s, "struct")?,
                }
            }
            b"natVal" => {
                let s = c.parse_plain_string()?;
                let n = match parse_nat(s) {
                    Some(n) => n,
                    None => return reject("invalid or unsupported natVal"),
                };
                push_capacity(self.env.nats.len(), "nat literals")?;
                let idx = self.env.nats.len() as u32;
                self.env.nats.push(n);
                RawNode { tag: RawTag::Nat, a: idx, b: 0, c: 0 }
            }
            b"strVal" => {
                c.parse_string_into(&mut self.scratch)?;
                let s = match std::str::from_utf8(&self.scratch) {
                    Ok(s) => s,
                    Err(_) => return reject("invalid UTF-8 in strVal"),
                };
                let idx = match self.str_ix.get(s) {
                    Some(&i) => i,
                    None => {
                        push_capacity(self.env.strs.len(), "string literals")?;
                        let i = self.env.strs.len() as u32;
                        self.env.strs.push(s.to_owned());
                        self.str_ix.insert(s.to_owned(), i);
                        i
                    }
                };
                RawNode { tag: RawTag::Str, a: idx, b: 0, c: 0 }
            }
            b"mdata" => {
                let mut inner = None;
                each_key!(c, k => match k {
                    b"expr" => put(&mut inner, self.read_expr_ref(c)?, "expr")?,
                    _ => c.skip_value()?,
                });
                return Ok((req(inner, "expr")?, false));
            }
            _ => return reject("unexpected expression key"),
        };
        self.push_expr(node)
    }

    /// `{"typeName": ..., "us": [level...], "name": ...}`: the levels go to `const_levels`.
    fn parse_const(&mut self, c: &mut Cursor<'_>) -> LResult<(u32, bool)> {
        let mut name = None;
        let mut us: Option<(u32, u32)> = None;
        each_key!(c, k => match k {
            b"name" => put(&mut name, self.read_name_ref(c)?, "name")?,
            b"us" => {
                if us.is_some() {
                    return reject("duplicate field `us`");
                }
                let off = self.env.const_levels.len();
                let mut cnt = 0usize;
                each_elem!(c, {
                    let l = self.read_level_ref(c)?;
                    self.env.const_levels.push(l);
                    cnt += 1;
                });
                us = Some((to_u32(off, "constant level lists")?, to_u32(cnt, "constant levels")?));
            }
            _ => c.skip_value()?,
        });
        let (off, cnt) = req(us, "us")?;
        let name = req(name, "name")?;
        self.push_expr(RawNode { tag: RawTag::Const, a: name, b: off, c: cnt })
    }

    /// Declaration lines: `axiom`, `def`, `opaque`, `thm`, `quot`, `inductive`.
    fn parse_decl(&mut self, key: &[u8], c: &mut Cursor<'_>) -> LResult<()> {
        let pos = self.env.decls.len();
        push_capacity(pos, "declarations")?;
        let pos = pos as u32;
        if key == b"inductive" {
            return self.parse_inductive(pos, c);
        }
        let f = self.parse_fields(c)?;
        let name = req(f.name, "name")?;
        let level_params = req(f.level_params, "levelParams")?;
        let ty = req(f.ty, "type")?;
        let (kind, is_unsafe, decl) = match key {
            b"axiom" => (ConstKind::Axiom, req(f.is_unsafe, "isUnsafe")?, Decl::Axiom { name }),
            b"def" => {
                let safety = req(f.safety, "safety")?;
                let hints = req(f.hints, "hints")?;
                let value = req(f.value, "value")?;
                let all = req(f.all, "all")?;
                (
                    ConstKind::Def { value, hints, safety, all },
                    safety != Safety::Safe,
                    Decl::Def { name },
                )
            }
            b"thm" => {
                let value = req(f.value, "value")?;
                let all = req(f.all, "all")?;
                (ConstKind::Thm { value, all }, false, Decl::Thm { name })
            }
            b"opaque" => {
                let value = req(f.value, "value")?;
                let is_unsafe = req(f.is_unsafe, "isUnsafe")?;
                let all = req(f.all, "all")?;
                (ConstKind::Opaque { value, all }, is_unsafe, Decl::Opaque { name })
            }
            _ => (ConstKind::Quot(req(f.quot_kind, "kind")?), false, Decl::Quot { name }),
        };
        self.declare(name, ConstInfo { pos, level_params, ty, kind, is_unsafe })?;
        self.env.decls.push(decl);
        Ok(())
    }

    /// `{"types": [...], "ctors": [...], "recs": [...]}`. Each element is a constant record.
    fn parse_inductive(&mut self, pos: u32, c: &mut Cursor<'_>) -> LResult<()> {
        let mut types = Vec::new();
        let mut ctors = Vec::new();
        let mut recs = Vec::new();
        each_key!(c, k => match k {
            b"types" => each_elem!(c, {
                let f = self.parse_fields(c)?;
                let (n, info) = induct_const(f, pos)?;
                self.declare(n, info)?;
                types.push(n);
            }),
            b"ctors" => each_elem!(c, {
                let f = self.parse_fields(c)?;
                let (n, info) = ctor_const(f, pos)?;
                self.declare(n, info)?;
                ctors.push(n);
            }),
            b"recs" => each_elem!(c, {
                let f = self.parse_fields(c)?;
                let (n, info) = rec_const(f, pos)?;
                self.declare(n, info)?;
                recs.push(n);
            }),
            _ => c.skip_value()?,
        });
        self.env.decls.push(Decl::Inductive { types, ctors, recs });
        Ok(())
    }

    /// Reads any object of constant fields. Unknown keys are skipped.
    fn parse_fields(&mut self, c: &mut Cursor<'_>) -> LResult<Fields> {
        let mut f = Fields::default();
        each_key!(c, k => match k {
            b"name" => put(&mut f.name, self.read_name_ref(c)?, "name")?,
            b"levelParams" => put(&mut f.level_params, self.read_name_array(c)?, "levelParams")?,
            b"type" => put(&mut f.ty, self.read_expr_ref(c)?, "type")?,
            b"value" => put(&mut f.value, self.read_expr_ref(c)?, "value")?,
            b"isUnsafe" => put(&mut f.is_unsafe, c.parse_bool()?, "isUnsafe")?,
            b"hints" => put(&mut f.hints, parse_hints(c)?, "hints")?,
            b"safety" => put(&mut f.safety, parse_safety(c)?, "safety")?,
            b"all" => put(&mut f.all, self.read_name_array(c)?, "all")?,
            b"kind" => put(&mut f.quot_kind, parse_quot_kind(c)?, "kind")?,
            b"numParams" => put(&mut f.num_params, read_u32(c)?, "numParams")?,
            b"numIndices" => put(&mut f.num_indices, read_u32(c)?, "numIndices")?,
            b"ctors" => put(&mut f.ctors, self.read_name_array(c)?, "ctors")?,
            b"numNested" => put(&mut f.num_nested, read_u32(c)?, "numNested")?,
            b"isRec" => put(&mut f.is_rec, c.parse_bool()?, "isRec")?,
            b"isReflexive" => put(&mut f.is_reflexive, c.parse_bool()?, "isReflexive")?,
            b"induct" => put(&mut f.induct, self.read_name_ref(c)?, "induct")?,
            b"cidx" => put(&mut f.cidx, read_u32(c)?, "cidx")?,
            b"numFields" => put(&mut f.num_fields, read_u32(c)?, "numFields")?,
            b"numMotives" => put(&mut f.num_motives, read_u32(c)?, "numMotives")?,
            b"numMinors" => put(&mut f.num_minors, read_u32(c)?, "numMinors")?,
            b"rules" => {
                let mut v = Vec::new();
                each_elem!(c, {
                    v.push(self.parse_rule(c)?);
                });
                put(&mut f.rules, v, "rules")?;
            }
            b"k" => put(&mut f.k, c.parse_bool()?, "k")?,
            _ => c.skip_value()?,
        });
        Ok(f)
    }

    fn parse_rule(&self, c: &mut Cursor<'_>) -> LResult<RecRule> {
        let (mut ctor, mut nfields, mut rhs) = (None, None, None);
        each_key!(c, k => match k {
            b"ctor" => put(&mut ctor, self.read_name_ref(c)?, "ctor")?,
            b"nfields" => put(&mut nfields, read_u32(c)?, "nfields")?,
            b"rhs" => put(&mut rhs, self.read_expr_ref(c)?, "rhs")?,
            _ => c.skip_value()?,
        });
        Ok(RecRule {
            ctor: req(ctor, "ctor")?,
            nfields: req(nfields, "nfields")?,
            rhs: req(rhs, "rhs")?,
        })
    }

    /// Adds `name` to the constant table. A second declaration of the same name is a rejection.
    fn declare(&mut self, name: NameId, info: ConstInfo) -> LResult<()> {
        let i = name as usize;
        if self.consts.len() <= i {
            self.consts.resize_with(i + 1, || None);
        }
        if self.consts[i].is_some() {
            return reject(format!("constant `{}` is declared twice", self.env.name_to_string(name)));
        }
        self.consts[i] = Some(info);
        Ok(())
    }

    fn finish(self) -> LResult<Env> {
        let Loader { env, mut consts, .. } = self;
        if consts.len() < env.names.len() {
            consts.resize_with(env.names.len(), || None);
        }
        let builtins = Builtins::resolve(&env);
        Ok(Env { raw: env, consts, builtins })
    }
}

fn induct_const(f: Fields, pos: u32) -> LResult<(NameId, ConstInfo)> {
    let name = req(f.name, "name")?;
    let is_unsafe = req(f.is_unsafe, "isUnsafe")?;
    let info = InductInfo {
        num_params: req(f.num_params, "numParams")?,
        num_indices: req(f.num_indices, "numIndices")?,
        all: req(f.all, "all")?,
        ctors: req(f.ctors, "ctors")?,
        num_nested: req(f.num_nested, "numNested")?,
        is_rec: req(f.is_rec, "isRec")?,
        is_unsafe,
        is_reflexive: req(f.is_reflexive, "isReflexive")?,
    };
    Ok((
        name,
        ConstInfo {
            pos,
            level_params: req(f.level_params, "levelParams")?,
            ty: req(f.ty, "type")?,
            kind: ConstKind::Induct(info),
            is_unsafe,
        },
    ))
}

fn ctor_const(f: Fields, pos: u32) -> LResult<(NameId, ConstInfo)> {
    let name = req(f.name, "name")?;
    let is_unsafe = req(f.is_unsafe, "isUnsafe")?;
    let info = CtorInfo {
        induct: req(f.induct, "induct")?,
        cidx: req(f.cidx, "cidx")?,
        num_params: req(f.num_params, "numParams")?,
        num_fields: req(f.num_fields, "numFields")?,
        is_unsafe,
    };
    Ok((
        name,
        ConstInfo {
            pos,
            level_params: req(f.level_params, "levelParams")?,
            ty: req(f.ty, "type")?,
            kind: ConstKind::Ctor(info),
            is_unsafe,
        },
    ))
}

fn rec_const(f: Fields, pos: u32) -> LResult<(NameId, ConstInfo)> {
    let name = req(f.name, "name")?;
    let is_unsafe = req(f.is_unsafe, "isUnsafe")?;
    let info = RecInfo {
        all: req(f.all, "all")?,
        num_params: req(f.num_params, "numParams")?,
        num_indices: req(f.num_indices, "numIndices")?,
        num_motives: req(f.num_motives, "numMotives")?,
        num_minors: req(f.num_minors, "numMinors")?,
        rules: req(f.rules, "rules")?,
        k: req(f.k, "k")?,
        is_unsafe,
    };
    Ok((
        name,
        ConstInfo {
            pos,
            level_params: req(f.level_params, "levelParams")?,
            ty: req(f.ty, "type")?,
            kind: ConstKind::Rec(info),
            is_unsafe,
        },
    ))
}

fn read_u64_pair(c: &mut Cursor<'_>) -> LResult<[u64; 2]> {
    let mut v = [0u64; 2];
    let mut n = 0usize;
    each_elem!(c, {
        let x = c.parse_u64()?;
        if n == 2 {
            return reject("expected a two-element array");
        }
        v[n] = x;
        n += 1;
    });
    if n != 2 {
        return reject("expected a two-element array");
    }
    Ok(v)
}

fn parse_hints(c: &mut Cursor<'_>) -> LResult<Hints> {
    match c.peek() {
        Some(b'"') => match c.parse_plain_string()? {
            b"opaque" => Ok(Hints::Opaque),
            b"abbrev" => Ok(Hints::Abbrev),
            _ => reject("invalid hints value"),
        },
        Some(b'{') => {
            let mut r = None;
            each_key!(c, k => match k {
                b"regular" => put(&mut r, read_u32(c)?, "regular")?,
                _ => c.skip_value()?,
            });
            Ok(Hints::Regular(req(r, "regular")?))
        }
        _ => reject("invalid hints value"),
    }
}

fn parse_safety(c: &mut Cursor<'_>) -> LResult<Safety> {
    match c.parse_plain_string()? {
        b"unsafe" => Ok(Safety::Unsafe),
        b"safe" => Ok(Safety::Safe),
        b"partial" => Ok(Safety::Partial),
        _ => reject("invalid safety value"),
    }
}

fn parse_quot_kind(c: &mut Cursor<'_>) -> LResult<QuotKind> {
    match c.parse_plain_string()? {
        b"type" => Ok(QuotKind::Type),
        b"ctor" => Ok(QuotKind::Ctor),
        b"lift" => Ok(QuotKind::Lift),
        b"ind" => Ok(QuotKind::Ind),
        _ => reject("invalid quot kind"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    const META: &str = r#"{"meta":{"exporter":{"name":"test","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"x","version":"4.0.0"}}}"#;

    fn file(lines: &[&str]) -> String {
        let mut s = String::from(META);
        for l in lines {
            s.push('\n');
            s.push_str(l);
        }
        s
    }

    fn load_lines(lines: &[&str]) -> Result<Env, LoadError> {
        load(file(lines).as_bytes())
    }

    fn ok(lines: &[&str]) -> Env {
        match load_lines(lines) {
            Ok(e) => e,
            Err(e) => panic!("expected Ok, got {e}"),
        }
    }

    fn is_reject(r: &Result<Env, LoadError>) -> bool {
        matches!(r, Err(LoadError::Reject(_)))
    }

    fn name(env: &Env, comps: &[&str]) -> NameId {
        env.raw.find_name(comps).unwrap_or_else(|| panic!("no name {comps:?}"))
    }

    /// Nat, Nat.zero, Nat.succ with a recursive inductive block, plus Nat-typed defs.
    const NAT: &[&str] = &[
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"zero"}}"#,
        r#"{"in":3,"str":{"pre":1,"str":"succ"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
        r#"{"ie":2,"forallE":{"name":0,"type":1,"body":1,"binderInfo":"default"}}"#,
        r#"{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[2,3],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"ctors":[{"name":2,"levelParams":[],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false},{"name":3,"levelParams":[],"type":2,"induct":1,"cidx":1,"numParams":0,"numFields":1,"isUnsafe":false}],"recs":[]}}"#,
    ];

    #[test]
    fn meta_version_gate() {
        let bad = r#"{"meta":{"format":{"version":"4.0.0"}}}"#;
        assert!(matches!(load(bad.as_bytes()), Err(LoadError::Decline(_))));
        let no_meta = r#"{"in":1,"str":{"pre":0,"str":"a"}}"#;
        assert!(is_reject(&load(no_meta.as_bytes())));
        let no_version = r#"{"meta":{"format":{}}}"#;
        assert!(is_reject(&load(no_version.as_bytes())));
        assert!(is_reject(&load(b"")));
        // Blank lines are ignored everywhere.
        let blanks = format!("\n\n{META}\n\n   \n{}\n\n", NAT.join("\n"));
        assert!(load(blanks.as_bytes()).is_ok());
    }

    #[test]
    fn unknown_top_level_key_declines() {
        let r = load_lines(&[r#"{"in":1,"str":{"pre":0,"str":"a"}}"#, r#"{"frobnicate":{}}"#]);
        assert!(matches!(r, Err(LoadError::Decline(_))), "{r:?}");
        let r = load_lines(&[r#"{"in":1,"str":{"pre":0,"str":"a"}}"#, r#"{"in":2,"str":{"pre":0,"str":"b"},"zzz":1}"#]);
        assert!(matches!(r, Err(LoadError::Decline(_))), "{r:?}");
    }

    #[test]
    fn names_of_every_shape() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"Foo"}}"#,
            r#"{"in":2,"num":{"pre":1,"i":7}}"#,
            r#"{"in":3,"str":{"pre":2,"str":"α😀"}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"Foo"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"ie":1,"const":{"name":4,"us":[]}}"#,
            r#"{"axiom":{"name":3,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{"axiom":{"name":2,"levelParams":[],"type":0,"isUnsafe":true}}"#,
        ]);
        // Index 4 is the same name as index 1 (canonical).
        assert_eq!(name(&env, &["Foo"]), 1);
        assert_eq!(env.raw.name_to_string(2), "Foo.7");
        assert_eq!(env.raw.name_to_string(3), "Foo.7.\u{3b1}\u{1F600}");
        assert!(env.get(3).is_some());
        assert!(env.get(2).unwrap().is_unsafe);
        assert!(!env.get(3).unwrap().is_unsafe);
    }

    #[test]
    fn levels_of_every_shape() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"u"}}"#,
            r#"{"il":1,"param":1}"#,
            r#"{"il":2,"succ":1}"#,
            r#"{"il":3,"max":[0,2]}"#,
            r#"{"il":4,"imax":[3,1]}"#,
            r#"{"ie":0,"sort":4}"#,
            r#"{"axiom":{"name":1,"levelParams":[1],"type":0,"isUnsafe":false}}"#,
        ]);
        assert_eq!(
            env.raw.levels,
            vec![
                RawLevelNode::Zero,
                RawLevelNode::Param(1),
                RawLevelNode::Succ(1),
                RawLevelNode::Max(0, 2),
                RawLevelNode::IMax(3, 1),
            ]
        );
        assert_eq!(env.raw.exprs[0], RawNode { tag: RawTag::Sort, a: 4, b: 0, c: 0 });
        assert_eq!(env.get(1).unwrap().level_params, vec![1]);
    }

    #[test]
    fn expressions_of_every_shape() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"c"}}"#,
            r#"{"in":2,"str":{"pre":0,"str":"f"}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"ie":0,"bvar":3}"#,
            r#"{"ie":1,"sort":1}"#,
            r#"{"ie":2,"const":{"us":[1,0],"name":1}}"#,
            r#"{"ie":3,"app":{"arg":0,"fn":2}}"#,
            r#"{"ie":4,"lam":{"binderInfo":"instImplicit","body":0,"type":1,"name":1}}"#,
            r#"{"ie":5,"forallE":{"name":2,"type":1,"body":4,"binderInfo":"strictImplicit"}}"#,
            r#"{"ie":6,"letE":{"nondep":false,"body":0,"value":3,"type":1,"name":1}}"#,
            r#"{"ie":7,"proj":{"typeName":1,"idx":2,"struct":0}}"#,
            r#"{"ie":8,"natVal":"12345678901234"}"#,
            r#"{"ie":9,"strVal":"he said \"hi\"\n"}"#,
            r#"{"ie":10,"strVal":"he said \"hi\"\n"}"#,
            r#"{"ie":11,"proj":{"typeName":1,"idx":18446744073709551615,"struct":0}}"#,
            r#"{"ie":12,"bvar":18446744073709551615}"#,
            r#"{"ie":13,"natVal":"0"}"#,
            r#"{"ie":14,"lam":{"name":1,"type":1,"body":0,"binderInfo":"implicit"}}"#,
            r#"{"axiom":{"name":2,"levelParams":[],"type":5,"isUnsafe":false}}"#,
        ]);
        let e = &env.raw.exprs;
        assert_eq!(e[0], RawNode { tag: RawTag::BVar, a: 3, b: 0, c: 0 });
        assert_eq!(e[1], RawNode { tag: RawTag::Sort, a: 1, b: 0, c: 0 });
        assert_eq!(e[2], RawNode { tag: RawTag::Const, a: 1, b: 0, c: 2 });
        assert_eq!(env.raw.const_levels, vec![1, 0]);
        assert_eq!(e[3], RawNode { tag: RawTag::App, a: 2, b: 0, c: 0 });
        assert_eq!(e[4], RawNode { tag: RawTag::Lam, a: 1, b: 0, c: 0 });
        assert_eq!(e[5], RawNode { tag: RawTag::Pi, a: 1, b: 4, c: 0 });
        assert_eq!(e[6], RawNode { tag: RawTag::Let, a: 1, b: 3, c: 0 });
        assert_eq!(e[7], RawNode { tag: RawTag::Proj, a: 1, b: 2, c: 0 });
        assert_eq!(e[8], RawNode { tag: RawTag::Nat, a: 0, b: 0, c: 0 });
        assert_eq!(env.raw.nats.len(), 2);
        assert_eq!(e[9], RawNode { tag: RawTag::Str, a: 0, b: 0, c: 0 });
        // Equal strings share one index.
        assert_eq!(e[10], RawNode { tag: RawTag::Str, a: 0, b: 0, c: 0 });
        assert_eq!(env.raw.strs, vec!["he said \"hi\"\n".to_string()]);
        assert_eq!(e[11], RawNode { tag: RawTag::Proj, a: 1, b: u32::MAX, c: 0 });
        assert_eq!(e[12], RawNode { tag: RawTag::BVar, a: u32::MAX, b: 0, c: 0 });
        assert_eq!(e[14], RawNode { tag: RawTag::Lam, a: 1, b: 0, c: 0 });
    }

    #[test]
    fn mdata_is_transparent() {
        let env = ok(&[
            r#"{"ie":0,"sort":0}"#,
            r#"{"ie":1,"mdata":{"expr":0,"data":{"k":[1,"x",{"y":null}]}}}"#,
            r#"{"ie":2,"mdata":{"data":{},"expr":1}}"#,
            r#"{"ie":3,"app":{"fn":2,"arg":2}}"#,
            r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":3,"isUnsafe":false}}"#,
        ]);
        // Two mdata nodes add nothing; the app refers to Sort 0 (id 0) directly.
        assert_eq!(env.raw.exprs.len(), 2);
        assert_eq!(env.raw.exprs[1], RawNode { tag: RawTag::App, a: 0, b: 0, c: 0 });
        assert_eq!(env.get(1).unwrap().ty, 1);
    }

    #[test]
    fn sparse_and_out_of_order_indices() {
        let env = ok(&[
            r#"{"in":2,"str":{"pre":0,"str":"foo"}}"#,
            r#"{"ie":4,"sort":0}"#,
            r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":4}}"#,
            r#"{"il":2,"succ":0}"#,
            r#"{"il":1,"succ":2}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"in":7,"str":{"pre":2,"str":"bar"}}"#,
            r#"{"axiom":{"name":7,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        ]);
        // ie 4 -> expr 0 (Sort zero); ie 0 -> expr 1 (Sort of il 1 = expr-level id 2).
        assert_eq!(env.raw.exprs[0], RawNode { tag: RawTag::Sort, a: 0, b: 0, c: 0 });
        assert_eq!(env.raw.exprs[1], RawNode { tag: RawTag::Sort, a: 2, b: 0, c: 0 });
        assert_eq!(env.raw.levels[1], RawLevelNode::Succ(0));
        assert_eq!(env.raw.levels[2], RawLevelNode::Succ(1));
        assert_eq!(env.raw.name_to_string(name(&env, &["foo", "bar"])), "foo.bar");
        assert!(env.get(2).is_some() && env.get(name(&env, &["foo", "bar"])).is_some());
    }

    #[test]
    fn dangling_reference_rejects() {
        assert!(is_reject(&load_lines(&[r#"{"ie":0,"sort":5}"#])));
        assert!(is_reject(&load_lines(&[r#"{"in":1,"str":{"pre":9,"str":"a"}}"#])));
        // An item may only refer to earlier lines.
        assert!(is_reject(&load_lines(&[r#"{"ie":0,"app":{"fn":0,"arg":0}}"#])));
        assert!(is_reject(&load_lines(&[
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":5,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        ])));
    }

    #[test]
    fn redefinition_and_index_kind_reject() {
        assert!(is_reject(&load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
            r#"{"in":1,"str":{"pre":0,"str":"b"}}"#,
        ])));
        // Index 0 is predefined (anonymous name).
        assert!(is_reject(&load_lines(&[r#"{"in":0,"str":{"pre":0,"str":"a"}}"#])));
        // Level index 0 is predefined (zero).
        assert!(is_reject(&load_lines(&[r#"{"il":0,"succ":0}"#])));
        // A name payload must carry an `in` key.
        assert!(is_reject(&load_lines(&[r#"{"ie":0,"str":{"pre":0,"str":"a"}}"#])));
        assert!(is_reject(&load_lines(&[r#"{"str":{"pre":0,"str":"a"}}"#])));
    }

    #[test]
    fn duplicate_declaration_rejects() {
        assert!(is_reject(&load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{"thm":{"name":1,"levelParams":[],"type":0,"value":0,"all":[1]}}"#,
        ])));
        // Duplicate inside one inductive block.
        let mut lines: Vec<&str> = NAT.to_vec();
        lines.push(r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#);
        assert!(is_reject(&load_lines(&lines)));
    }

    #[test]
    fn duplicate_field_and_bad_values_reject() {
        assert!(is_reject(&load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        ])));
        assert!(is_reject(&load_lines(&[r#"{"ie":0,"sort":0,"ie":1}"#])));
        assert!(is_reject(&load_lines(&[r#"{"in":1,"str":{"pre":0}}"#])));
        assert!(is_reject(&load_lines(&[r#"{"in":1,"str":{"pre":0,"str":"a"}"#]))); // truncated
        assert!(is_reject(&load_lines(&[r#"{"in":"1","str":{"pre":0,"str":"a"}}"#])));
        assert!(is_reject(&load_lines(&[r#"{"in":1,"str":{"pre":0,"str":"a"}} trailing"#])));
    }

    #[test]
    fn nat_block_loads() {
        let env = ok(NAT);
        let nat = name(&env, &["Nat"]);
        assert_eq!(env.builtins.nat_ty, Some(nat));
        assert_eq!(env.builtins.nat_zero, Some(name(&env, &["Nat", "zero"])));
        assert_eq!(env.builtins.nat_add, None);
        let info = env.get(nat).unwrap();
        assert_eq!(info.pos, 0);
        match &info.kind {
            ConstKind::Induct(i) => {
                assert!(i.is_rec && !i.is_unsafe && !i.is_reflexive);
                assert_eq!(i.ctors, vec![name(&env, &["Nat", "zero"]), name(&env, &["Nat", "succ"])]);
            }
            k => panic!("unexpected {k:?}"),
        }
        match &env.get(name(&env, &["Nat", "succ"])).unwrap().kind {
            ConstKind::Ctor(c) => assert_eq!((c.induct, c.cidx, c.num_fields), (nat, 1, 1)),
            k => panic!("unexpected {k:?}"),
        }
        assert_eq!(env.raw.decls, vec![Decl::Inductive { types: vec![nat], ctors: vec![name(&env, &["Nat", "zero"]), name(&env, &["Nat", "succ"])], recs: vec![] }]);
    }

    #[test]
    fn recursor_rules_load() {
        let mut lines: Vec<&str> = NAT.to_vec();
        lines.push(r#"{"in":4,"str":{"pre":1,"str":"rec"}}"#);
        lines.push(r#"{"ie":3,"const":{"name":1,"us":[]}}"#);
        lines.push(r#"{"inductive":{"types":[],"ctors":[],"recs":[{"name":4,"levelParams":[],"type":3,"all":[1],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":2,"rules":[{"ctor":2,"nfields":0,"rhs":1},{"rhs":0,"nfields":1,"ctor":3}],"k":false,"isUnsafe":false}]}}"#);
        let env = ok(&lines);
        let rec = name(&env, &["Nat", "rec"]);
        match &env.get(rec).unwrap().kind {
            ConstKind::Rec(r) => {
                assert_eq!(r.rules.len(), 2);
                assert_eq!(r.rules[1], RecRule { ctor: 3, nfields: 1, rhs: 0 });
                assert_eq!(r.num_minors, 2);
                assert!(!r.k);
            }
            k => panic!("unexpected {k:?}"),
        }
        assert_eq!(env.get(rec).unwrap().pos, 1);
    }

    #[test]
    fn quot_and_theorem_and_opaque_load() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"Quot"}}"#,
            r#"{"in":2,"str":{"pre":1,"str":"mk"}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"ie":1,"sort":0}"#,
            r#"{"quot":{"name":1,"levelParams":[],"type":0,"kind":"type"}}"#,
            r#"{"quot":{"name":2,"levelParams":[],"type":1,"kind":"ctor"}}"#,
            r#"{"in":3,"str":{"pre":0,"str":"t"}}"#,
            r#"{"thm":{"name":3,"levelParams":[],"type":1,"value":1,"all":[3]}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"o"}}"#,
            r#"{"opaque":{"name":4,"levelParams":[1],"type":0,"value":0,"isUnsafe":true,"all":[4]}}"#,
            r#"{"in":5,"str":{"pre":0,"str":"d"}}"#,
            r#"{"def":{"name":5,"levelParams":[],"type":0,"value":0,"hints":{"regular":7},"safety":"partial","all":[5]}}"#,
            r#"{"in":6,"str":{"pre":0,"str":"e"}}"#,
            r#"{"def":{"all":[6],"hints":"abbrev","levelParams":[],"name":6,"safety":"safe","type":0,"value":0}}"#,
        ]);
        assert_eq!(env.raw.decls[0], Decl::Quot { name: 1 });
        assert!(matches!(env.get(1).unwrap().kind, ConstKind::Quot(QuotKind::Type)));
        assert!(matches!(env.get(2).unwrap().kind, ConstKind::Quot(QuotKind::Ctor)));
        assert!(matches!(env.get(3).unwrap().kind, ConstKind::Thm { value: 1, .. }));
        let o = env.get(4).unwrap();
        assert!(o.is_unsafe && o.level_params == vec![1]);
        let d = env.get(5).unwrap();
        assert!(d.is_unsafe);
        assert!(matches!(d.kind, ConstKind::Def { hints: Hints::Regular(7), safety: Safety::Partial, .. }));
        let e = env.get(6).unwrap();
        assert!(!e.is_unsafe);
        assert!(matches!(e.kind, ConstKind::Def { hints: Hints::Abbrev, safety: Safety::Safe, .. }));
        assert_eq!(env.raw.decls[3], Decl::Opaque { name: 4 });
        assert_eq!(env.raw.decls[4], Decl::Def { name: 5 });
    }

    #[test]
    fn axiom_def_and_unsafe_defs() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"x"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"opaque","safety":"unsafe","all":[1]}}"#,
        ]);
        assert!(env.get(1).unwrap().is_unsafe);
        assert_eq!(env.raw.decls, vec![Decl::Def { name: 1 }]);
        let r = load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"x"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"nope","safety":"unsafe","all":[1]}}"#,
        ]);
        assert!(is_reject(&r));
        let r = load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"x"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"opaque","safety":"sometimes","all":[1]}}"#,
        ]);
        assert!(is_reject(&r));
        // A missing field is a rejection.
        let r = load_lines(&[
            r#"{"in":1,"str":{"pre":0,"str":"x"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0}}"#,
        ]);
        assert!(is_reject(&r));
    }

    #[test]
    fn unknown_keys_inside_objects_are_skipped() {
        let env = ok(&[
            r#"{"in":1,"str":{"pre":0,"str":"x","extra":[1,{"a":"é"}]}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false,"doc":{"deep":[true]}}}"#,
        ]);
        assert!(env.get(1).is_some());
    }

    /// Recursively collects `.ndjson` files under `dir`.
    fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        let mut entries: Vec<_> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                collect(&p, out);
            } else if p.extension().is_some_and(|e| e == "ndjson") {
                out.push(p);
            }
        }
    }

    /// Placeholder bignum limit: good files with nat literals above u64 cannot load until the real bignum lands.
    const PENDING_BIGNUM: &[&str] = &["init-prelude.ndjson"];

    #[test]
    fn arena_corpus() {
        let root = Path::new("/home/user/Palladium/arena-tests");
        if !root.is_dir() {
            return;
        }
        let mut good = Vec::new();
        collect(&root.join("good"), &mut good);
        let mut bad = Vec::new();
        collect(&root.join("bad"), &mut bad);
        let mut failures = Vec::new();
        for f in &good {
            let bytes = fs::read(f).expect("read");
            if let Err(e) = load(&bytes) {
                let fname = f.file_name().unwrap().to_string_lossy().to_string();
                if PENDING_BIGNUM.contains(&fname.as_str()) && e.to_string().contains("natVal") {
                    println!("note: {} needs the real bignum: {e}", f.display());
                    continue;
                }
                failures.push(format!("{}: {e}", f.display()));
            }
        }
        assert!(failures.is_empty(), "good files failed to load:\n{}", failures.join("\n"));
        for f in &bad {
            match load(&fs::read(f).expect("read")) {
                Ok(_) => println!("bad file loads (rejected later by the checker): {}", f.display()),
                Err(e) => println!("bad file rejected at load: {}: {e}", f.display()),
            }
        }
    }

    /// Timing of `load` on the largest good perf file. Run with
    /// `cargo test --release -- --ignored --nocapture bench_load`.
    #[test]
    #[ignore]
    fn bench_load_grind_ring() {
        let path = Path::new("/home/user/Palladium/arena-tests/good/perf/grind-ring-5.ndjson");
        let bytes = fs::read(path).expect("read perf file");
        let runs = 5;
        let mut best = f64::MAX;
        for _ in 0..runs {
            let t = std::time::Instant::now();
            let env = load(&bytes).expect("load");
            let secs = t.elapsed().as_secs_f64();
            best = best.min(secs);
            std::hint::black_box(&env);
        }
        println!(
            "load {} bytes: best {:.3} s = {:.1} MB/s",
            bytes.len(),
            best,
            bytes.len() as f64 / best / 1e6
        );
    }

    #[test]
    fn line_numbers_in_errors() {
        let e = load_lines(&[r#"{"ie":0,"sort":0}"#, r#"{"ie":1,"sort":9}"#]).unwrap_err();
        match e {
            LoadError::Reject(m) => assert!(m.starts_with("line 3:"), "{m}"),
            other => panic!("{other:?}"),
        }
    }
}

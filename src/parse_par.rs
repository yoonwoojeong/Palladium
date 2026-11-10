//! Parallel export loader. `load_parallel` returns exactly what `parse::load`
//! returns, using worker threads and a merge.
//!
//! The file is split at newlines into chunks. Each chunk runs the same line
//! grammar as the sequential loader (`parse::item_line`) with the `Chunk` sink,
//! which records raw records and checks references under the assumption that
//! the file is *dense*: the items of each index namespace carry consecutive
//! indices, and a reference is valid when it names an item defined earlier.
//!
//! Names are interned by one thread while the workers parse, in file order
//! (their canonical ids must equal their file indices, so every name must be
//! new). The merge then checks the density across chunks, remaps the
//! chunk-local string, nat and constant-level indices, and fills the expression
//! and level vectors in parallel. A chunk that finds anything else (a reference
//! it cannot resolve locally, an error, an `mdata` alias, a duplicate name or
//! constant) makes the whole parallel attempt fail, and the result is the
//! sequential `load` of the same bytes. The outcome (Ok, Reject or Decline,
//! with the same message) is therefore the sequential one by construction.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::thread;

use crate::bignat::BigNat;
use crate::env::*;
use crate::parse::{find_newline, item_line, lines, load, meta_line, reject, trim, LResult, LoadError, Ns, Sink};

/// Default chunk size in bytes.
pub const CHUNK_BYTES: usize = 64 << 20;

/// Loads an export with `threads` workers. Same result as `parse::load`.
pub fn load_parallel(bytes: &[u8], threads: usize) -> Result<Env, LoadError> {
    load_parallel_with(bytes, threads, CHUNK_BYTES)
}

/// `load_parallel` with an explicit chunk size (tests use tiny chunks).
pub fn load_parallel_with(bytes: &[u8], threads: usize, chunk_bytes: usize) -> Result<Env, LoadError> {
    match try_parallel(bytes, threads.max(1), chunk_bytes.max(1)) {
        Some(env) => Ok(env),
        None => {
            if std::env::var_os("PALLADIUM_TRACE").is_some() {
                eprintln!("trace: parallel load fell back to the sequential loader");
            }
            load(bytes)
        }
    }
}

/// Parallel attempt. `None` means "use the sequential loader".
fn try_parallel(bytes: &[u8], threads: usize, chunk_bytes: usize) -> Option<Env> {
    // The meta line is the first non-empty line; the sequential loader checks it.
    let mut pos = 0usize;
    let body_start = loop {
        if pos >= bytes.len() {
            return None;
        }
        let end = find_newline(&bytes[pos..]).map_or(bytes.len(), |p| pos + p);
        let line = trim(&bytes[pos..end]);
        if line.is_empty() {
            pos = end + 1;
            continue;
        }
        meta_line(line).ok()?;
        break (end + 1).min(bytes.len());
    };
    let trace = std::env::var_os("PALLADIUM_TRACE").is_some();
    let t0 = std::time::Instant::now();
    let chunks = split_chunks(&bytes[body_start..], chunk_bytes);
    let (results, names) = parse_all(&chunks, threads, bytes.len())?;
    let t1 = t0.elapsed();
    let env = merge(results, names, threads)?;
    if trace {
        eprintln!(
            "trace: parallel: {} chunks, parse and names {:.3}s, merge {:.3}s",
            chunks.len(),
            t1.as_secs_f64(),
            (t0.elapsed() - t1).as_secs_f64()
        );
    }
    Some(env)
}

/// Splits `body` into pieces of about `chunk_bytes`, each ending just after a newline.
fn split_chunks(body: &[u8], chunk_bytes: usize) -> Vec<&[u8]> {
    let mut out = Vec::new();
    let mut start = 0usize;
    while start < body.len() {
        let mut end = body.len().min(start.saturating_add(chunk_bytes));
        if end < body.len() {
            end = match find_newline(&body[end..]) {
                Some(p) => end + p + 1,
                None => body.len(),
            };
        }
        out.push(&body[start..end]);
        start = end;
    }
    out
}

/// Names of one chunk: prefixes, payloads and the bytes they point into.
type NameBatch = (usize, Vec<WName>, Vec<u8>);

/// Parses every chunk on `threads` workers while a further thread interns the
/// names in file order. `None` if any chunk fails, a worker panics, or the
/// names are not fresh.
fn parse_all(chunks: &[&[u8]], threads: usize, file_len: usize) -> Option<(Vec<Chunk>, RawEnv)> {
    let next = AtomicUsize::new(0);
    let failed = AtomicBool::new(false);
    let workers = threads.min(chunks.len()).max(1);
    let (tx, rx) = mpsc::channel::<NameBatch>();
    let (outs, names) = thread::scope(|s| {
        let total = chunks.len();
        let names_thread = s.spawn(move || intern_stream(rx, total, file_len));
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                let tx = tx.clone();
                let (next, failed) = (&next, &failed);
                s.spawn(move || {
                    let mut mine = Vec::new();
                    loop {
                        if failed.load(Ordering::Relaxed) {
                            break;
                        }
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= total {
                            break;
                        }
                        match parse_chunk(chunks[i]) {
                            Ok(mut c) => {
                                let names = std::mem::take(&mut c.names);
                                let buf = std::mem::take(&mut c.names_buf);
                                let _ = tx.send((i, names, buf));
                                mine.push((i, c));
                            }
                            Err(_) => {
                                failed.store(true, Ordering::Relaxed);
                                return None;
                            }
                        }
                    }
                    Some(mine)
                })
            })
            .collect();
        drop(tx);
        let outs: Vec<Option<Vec<(usize, Chunk)>>> = handles.into_iter().map(|h| h.join().ok().flatten()).collect();
        (outs, names_thread.join().ok().flatten())
    });
    if failed.load(Ordering::Relaxed) {
        return None;
    }
    let mut slots: Vec<Option<Chunk>> = (0..chunks.len()).map(|_| None).collect();
    for part in outs {
        for (i, c) in part? {
            slots[i] = Some(c);
        }
    }
    let chunks: Vec<Chunk> = slots.into_iter().collect::<Option<_>>()?;
    Some((chunks, names?))
}

/// Interns name batches in file order as they arrive. Returns the name table
/// when every batch was received and every name was new with the expected id.
fn intern_stream(rx: mpsc::Receiver<NameBatch>, total: usize, file_len: usize) -> Option<RawEnv> {
    let mut env = RawEnv::new();
    env.reserve_names(file_len / 512);
    let mut pending: BTreeMap<usize, (Vec<WName>, Vec<u8>)> = BTreeMap::new();
    let mut next = 0usize;
    // File index of the next name: names start after the predefined 0.
    let mut first: u64 = 1;
    let mut ok = true;
    for (i, names, buf) in rx {
        pending.insert(i, (names, buf));
        while let Some((names, buf)) = pending.remove(&next) {
            let count = names.len() as u64;
            ok = ok && intern_batch(&mut env, names, &buf, first);
            first += count;
            next += 1;
        }
    }
    (ok && next == total).then_some(env)
}

/// Interns the names of one chunk. The `j`-th name must be new and get file index `first + j`.
fn intern_batch(env: &mut RawEnv, names: Vec<WName>, buf: &[u8], first: u64) -> bool {
    for (j, w) in names.into_iter().enumerate() {
        let (id, fresh) = match w {
            WName::Str(p, off, len) => {
                let Some(bytes) = buf.get(off as usize..off as usize + len as usize) else {
                    return false;
                };
                let Ok(s) = std::str::from_utf8(bytes) else {
                    return false;
                };
                env.intern_str(p, s)
            }
            WName::Num(p, n) => env.intern_num(p, n),
        };
        if !fresh || id as u64 != first + j as u64 {
            return false;
        }
    }
    true
}

fn parse_chunk(bytes: &[u8]) -> LResult<Chunk> {
    let mut ch = Chunk::default();
    for line in lines(bytes) {
        let l = trim(line);
        if !l.is_empty() {
            item_line(&mut ch, l)?;
        }
    }
    Ok(ch)
}

/// Per namespace, what one chunk saw.
#[derive(Default, Clone, Copy)]
struct NsState {
    /// File index of the first item of this namespace in the chunk.
    first: Option<u64>,
    /// Items defined in the chunk. They have indices `first .. first + count`.
    count: u64,
    /// Largest reference made before the chunk's first item of this namespace.
    /// It must name an item of an earlier chunk, which the merge checks.
    pre_max: Option<u64>,
}

enum WName {
    /// Prefix, and the bytes `off .. off + len` of the chunk's name buffer.
    Str(NameId, u32, u32),
    Num(NameId, u64),
}

/// The records of one chunk. References are global file indices, checked
/// against the chunk's own items; the merge checks the rest.
#[derive(Default)]
struct Chunk {
    ns: [NsState; 3],
    names: Vec<WName>,
    names_buf: Vec<u8>,
    levels: Vec<RawLevelNode>,
    exprs: Vec<RawNode>,
    nats: Vec<BigNat>,
    /// Local indices (no deduplication across chunks).
    strs: Vec<String>,
    /// Constant-level lists; `Const` nodes hold chunk-local offsets.
    const_levels: Vec<RawLevel>,
    /// Declaration positions are chunk-local.
    decls: Vec<Decl>,
    consts: Vec<(NameId, ConstInfo)>,
    scratch: Vec<u8>,
}

impl Chunk {
    /// A reference to file index `idx` in namespace `ns`, made by the grammar.
    fn check_ref(&mut self, ns: Ns, idx: u64) -> LResult<u32> {
        if idx > u32::MAX as u64 {
            return reject("index out of range");
        }
        let st = &mut self.ns[ns as usize];
        match st.first {
            Some(f) => {
                if idx < f + st.count {
                    Ok(idx as u32)
                } else {
                    reject("reference to an item that is not defined yet")
                }
            }
            None => {
                st.pre_max = Some(st.pre_max.map_or(idx, |m| m.max(idx)));
                Ok(idx as u32)
            }
        }
    }
}

fn utf8(s: &[u8]) -> LResult<&str> {
    std::str::from_utf8(s).or_else(|_| reject("invalid UTF-8 in string"))
}

impl Sink for Chunk {
    fn scratch(&mut self) -> &mut Vec<u8> {
        &mut self.scratch
    }

    fn name_ref(&mut self, idx: u64) -> LResult<NameId> {
        if idx == 0 {
            return Ok(0);
        }
        self.check_ref(Ns::Name, idx)
    }

    fn level_ref(&mut self, idx: u64) -> LResult<RawLevel> {
        if idx == 0 {
            return Ok(0);
        }
        self.check_ref(Ns::Level, idx)
    }

    fn expr_ref(&mut self, idx: u64) -> LResult<RawExpr> {
        self.check_ref(Ns::Expr, idx)
    }

    fn str_name(&mut self, pre: NameId) -> LResult<(NameId, bool)> {
        let s = utf8(&self.scratch)?;
        let off = u32::try_from(self.names_buf.len()).or_else(|_| reject("name buffer too large"))?;
        let len = u32::try_from(s.len()).or_else(|_| reject("name too long"))?;
        self.names_buf.extend_from_slice(s.as_bytes());
        self.names.push(WName::Str(pre, off, len));
        Ok((0, true))
    }

    fn num_name(&mut self, pre: NameId, n: u64) -> LResult<(NameId, bool)> {
        self.names.push(WName::Num(pre, n));
        Ok((0, true))
    }

    fn str_lit(&mut self) -> LResult<u32> {
        let s = utf8(&self.scratch)?.to_owned();
        let i = self.strs.len();
        self.strs.push(s);
        Ok(i as u32)
    }

    fn push_level(&mut self, node: RawLevelNode) -> LResult<(RawLevel, bool)> {
        self.levels.push(node);
        Ok((0, true))
    }

    fn push_expr(&mut self, node: RawNode) -> LResult<(RawExpr, bool)> {
        self.exprs.push(node);
        Ok((0, true))
    }

    fn push_nat(&mut self, n: BigNat) -> LResult<u32> {
        let i = self.nats.len();
        self.nats.push(n);
        Ok(i as u32)
    }

    fn const_levels_len(&self) -> usize {
        self.const_levels.len()
    }

    fn push_const_level(&mut self, l: RawLevel) -> LResult<()> {
        self.const_levels.push(l);
        Ok(())
    }

    fn decl_count(&self) -> usize {
        self.decls.len()
    }

    fn push_decl(&mut self, d: Decl) -> LResult<()> {
        self.decls.push(d);
        Ok(())
    }

    fn declare(&mut self, name: NameId, info: ConstInfo) -> LResult<()> {
        self.consts.push((name, info));
        Ok(())
    }

    fn define(&mut self, ns: Ns, idx: u64, _id: u32, fresh: bool) -> LResult<()> {
        // A non-fresh node (an `mdata` alias) needs the sequential index table.
        if !fresh {
            return reject("alias index");
        }
        let st = &mut self.ns[ns as usize];
        match st.first {
            None => st.first = Some(idx),
            Some(f) => {
                if idx != f + st.count {
                    return reject("sparse or out-of-order index");
                }
            }
        }
        st.count += 1;
        Ok(())
    }
}

/// Chunk output that a fill job moves into the final vectors, remapping chunk-local indices.
struct Fill<'a> {
    exprs: Vec<RawNode>,
    levels: Vec<RawLevelNode>,
    ex_dst: &'a mut [RawNode],
    lv_dst: &'a mut [RawLevelNode],
    smap: Vec<u32>,
    cl_base: u32,
    nat_base: u32,
}

fn fill(job: Fill<'_>) -> Option<()> {
    let Fill { exprs, levels, ex_dst, lv_dst, smap, cl_base, nat_base } = job;
    lv_dst.copy_from_slice(&levels);
    for (d, mut n) in ex_dst.iter_mut().zip(exprs) {
        match n.tag {
            RawTag::Const => n.b = n.b.checked_add(cl_base)?,
            RawTag::Nat => n.a = n.a.checked_add(nat_base)?,
            RawTag::Str => n.a = *smap.get(n.a as usize)?,
            _ => {}
        }
        *d = n;
    }
    Some(())
}

/// Appends the chunks in file order, checking density and remapping chunk-local indices.
/// `None` means the file needs the sequential loader.
fn merge(chunks: Vec<Chunk>, mut env: RawEnv, threads: usize) -> Option<Env> {
    let mut consts: Vec<Option<ConstInfo>> = Vec::new();
    let mut str_ix: HashMap<String, u32> = HashMap::new();
    // Next file index per namespace: names and levels start after the predefined 0.
    let mut base: [u64; 3] = [1, 1, 0];
    let mut fills: Vec<(Vec<RawNode>, Vec<RawLevelNode>, Vec<u32>, u32, u32)> = Vec::with_capacity(chunks.len());
    // Level 0 (zero) is predefined.
    let (mut n_exprs, mut n_levels) = (0usize, 1usize);
    for ch in chunks {
        let Chunk { ns, levels, exprs, nats, strs, const_levels, decls, consts: cs, .. } = ch;
        for k in 0..3 {
            let st = ns[k];
            if st.first.is_some_and(|f| f != base[k]) {
                return None;
            }
            if st.pre_max.is_some_and(|p| p >= base[k]) {
                return None;
            }
        }
        for k in 0..3 {
            base[k] += ns[k].count;
        }
        let mut smap = Vec::with_capacity(strs.len());
        for s in strs {
            let i = match str_ix.get(&s) {
                Some(&i) => i,
                None => {
                    let i = u32::try_from(env.strs.len()).ok()?;
                    env.strs.push(s.clone());
                    str_ix.insert(s, i);
                    i
                }
            };
            smap.push(i);
        }
        let cl_base = u32::try_from(env.const_levels.len()).ok()?;
        let nat_base = u32::try_from(env.nats.len()).ok()?;
        env.nats.extend(nats);
        env.const_levels.extend_from_slice(&const_levels);
        let db = u32::try_from(env.decls.len()).ok()?;
        env.decls.extend(decls);
        for (name, mut info) in cs {
            info.pos = info.pos.checked_add(db)?;
            let i = name as usize;
            if consts.len() <= i {
                consts.resize_with(i + 1, || None);
            }
            if consts[i].is_some() {
                return None;
            }
            consts[i] = Some(info);
        }
        n_exprs += exprs.len();
        n_levels += levels.len();
        fills.push((exprs, levels, smap, cl_base, nat_base));
    }
    let mut exprs_out = vec![RawNode { tag: RawTag::BVar, a: 0, b: 0, c: 0 }; n_exprs];
    let mut levels_out = vec![RawLevelNode::Zero; n_levels];
    {
        let mut ex_rest: &mut [RawNode] = &mut exprs_out;
        let mut lv_rest: &mut [RawLevelNode] = &mut levels_out[1..];
        let mut buckets: Vec<Vec<Fill>> = (0..threads.max(1)).map(|_| Vec::new()).collect();
        let workers = buckets.len();
        for (i, (exprs, levels, smap, cl_base, nat_base)) in fills.into_iter().enumerate() {
            let (ex_dst, ex_tail) = std::mem::take(&mut ex_rest).split_at_mut(exprs.len());
            ex_rest = ex_tail;
            let (lv_dst, lv_tail) = std::mem::take(&mut lv_rest).split_at_mut(levels.len());
            lv_rest = lv_tail;
            buckets[i % workers].push(Fill { exprs, levels, ex_dst, lv_dst, smap, cl_base, nat_base });
        }
        let filled = thread::scope(|s| {
            let hs: Vec<_> = buckets
                .into_iter()
                .map(|b| s.spawn(move || b.into_iter().all(|job| fill(job).is_some())))
                .collect();
            hs.into_iter().all(|h| h.join().unwrap_or(false))
        });
        if !filled {
            return None;
        }
    }
    env.exprs = exprs_out;
    env.levels = levels_out;
    if consts.len() < env.names.len() {
        consts.resize_with(env.names.len(), || None);
    }
    let builtins = Builtins::resolve(&env);
    Some(Env { raw: env, consts, builtins })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    const META: &str = r#"{"meta":{"exporter":{"name":"test","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"x","version":"4.0.0"}}}"#;

    /// A dense export with names, levels, expressions, a recursive inductive and theorems.
    const DENSE: &[&str] = &[
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"zero"}}"#,
        r#"{"in":3,"str":{"pre":1,"str":"succ"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
        r#"{"ie":2,"forallE":{"name":0,"type":1,"body":1,"binderInfo":"default"}}"#,
        r#"{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[2,3],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"ctors":[{"name":2,"levelParams":[],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false},{"name":3,"levelParams":[],"type":2,"induct":1,"cidx":1,"numParams":0,"numFields":1,"isUnsafe":false}],"recs":[]}}"#,
        r#"{"in":4,"str":{"pre":0,"str":"f"}}"#,
        r#"{"ie":3,"lam":{"name":0,"type":1,"body":1,"binderInfo":"default"}}"#,
        r#"{"ie":4,"app":{"fn":3,"arg":1}}"#,
        r#"{"ie":5,"natVal":"12345678901234567890"}"#,
        r#"{"ie":6,"strVal":"hello"}"#,
        r#"{"ie":7,"strVal":"hello"}"#,
        r#"{"ie":8,"strVal":"other"}"#,
        r#"{"in":5,"num":{"pre":4,"i":7}}"#,
        r#"{"il":2,"param":5}"#,
        r#"{"il":3,"max":[2,1]}"#,
        r#"{"in":6,"str":{"pre":0,"str":"u"}}"#,
        r#"{"axiom":{"name":4,"levelParams":[6],"type":2,"isUnsafe":false}}"#,
        r#"{"def":{"name":5,"levelParams":[],"type":0,"value":4,"hints":{"regular":3},"safety":"safe","all":[5]}}"#,
        r#"{"ie":9,"proj":{"typeName":1,"idx":0,"struct":5}}"#,
        r#"{"ie":10,"sort":3}"#,
        r#"{"in":7,"str":{"pre":0,"str":"t"}}"#,
        r#"{"thm":{"name":7,"levelParams":[],"type":10,"value":9,"all":[7]}}"#,
    ];

    fn file(lines: &[&str]) -> String {
        let mut s = String::from(META);
        for l in lines {
            s.push('\n');
            s.push_str(l);
        }
        s
    }

    fn same_env(a: &Env, b: &Env) -> bool {
        a.raw.names == b.raw.names
            && a.raw.levels == b.raw.levels
            && a.raw.exprs == b.raw.exprs
            && a.raw.const_levels == b.raw.const_levels
            && a.raw.nats == b.raw.nats
            && a.raw.strs == b.raw.strs
            && a.raw.decls == b.raw.decls
            && a.consts == b.consts
            && a.builtins == b.builtins
    }

    /// Asserts that the parallel loader agrees with the sequential one for these bytes.
    fn agree(bytes: &[u8], threads: usize, chunk: usize) {
        let seq = load(bytes);
        let par = load_parallel_with(bytes, threads, chunk);
        match (&seq, &par) {
            (Ok(a), Ok(b)) => assert!(same_env(a, b), "envs differ (chunk {chunk})"),
            (Err(a), Err(b)) => assert_eq!(a, b, "errors differ (chunk {chunk})"),
            _ => panic!("outcomes differ (chunk {chunk}): seq {:?} par {:?}", seq.as_ref().err(), par.as_ref().err()),
        }
    }

    /// Whether the parallel path (not the fallback) accepts the bytes.
    fn parallel_accepts(bytes: &[u8], chunk: usize) -> bool {
        try_parallel(bytes, 2, chunk).is_some()
    }

    #[test]
    fn dense_file_takes_the_parallel_path() {
        let text = file(DENSE);
        assert!(parallel_accepts(text.as_bytes(), 16));
        assert!(parallel_accepts(text.as_bytes(), 1 << 20));
    }

    #[test]
    fn every_chunk_boundary_agrees() {
        let text = file(DENSE);
        let bytes = text.as_bytes();
        for chunk in 1..=bytes.len() {
            agree(bytes, 3, chunk);
        }
    }

    #[test]
    fn chunk_boundaries_with_blank_lines_crlf_and_no_final_newline() {
        let mut text = String::from("\n\n");
        text.push_str(META);
        text.push_str("\r\n   \r\n");
        for l in DENSE {
            text.push_str(l);
            text.push_str("\r\n\n");
        }
        // Final line without a newline.
        text.push_str(r#"{"ie":11,"sort":0}"#);
        let bytes = text.as_bytes();
        for chunk in 1..=bytes.len().min(400) {
            agree(bytes, 2, chunk);
        }
        agree(bytes, 4, 1 << 20);
    }

    #[test]
    fn irregular_files_fall_back_and_agree() {
        let cases: Vec<Vec<&str>> = vec![
            // Sparse expression indices.
            vec![r#"{"ie":0,"sort":0}"#, r#"{"ie":5,"sort":0}"#],
            // Out of order items.
            vec![r#"{"ie":1,"sort":0}"#, r#"{"ie":0,"sort":0}"#],
            // Duplicate name content: the second is not fresh.
            vec![
                r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
                r#"{"in":2,"str":{"pre":0,"str":"a"}}"#,
                r#"{"ie":0,"sort":0}"#,
                r#"{"axiom":{"name":2,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            ],
            // mdata alias.
            vec![r#"{"ie":0,"sort":0}"#, r#"{"ie":1,"mdata":{"expr":0}}"#, r#"{"ie":2,"app":{"fn":1,"arg":0}}"#],
            // Forward reference.
            vec![r#"{"ie":0,"app":{"fn":1,"arg":0}}"#, r#"{"ie":1,"sort":0}"#],
            // Duplicate declaration.
            vec![
                r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
                r#"{"ie":0,"sort":0}"#,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
                r#"{"thm":{"name":1,"levelParams":[],"type":0,"value":0,"all":[1]}}"#,
            ],
            // Parse error and unknown key.
            vec![r#"{"ie":0,"sort":0}"#, r#"{"ie":1,"sort":"#],
            vec![r#"{"ie":0,"sort":0}"#, r#"{"frob":{}}"#],
            // Index 0 is predefined.
            vec![r#"{"in":0,"str":{"pre":0,"str":"a"}}"#],
        ];
        for lines in &cases {
            let text = file(lines);
            for chunk in [1usize, 17, 1 << 20] {
                agree(text.as_bytes(), 2, chunk);
            }
        }
        assert!(!parallel_accepts(file(&[r#"{"ie":0,"sort":0}"#, r#"{"ie":5,"sort":0}"#]).as_bytes(), 1 << 20));
    }

    #[test]
    fn bad_meta_and_empty_input_agree() {
        for text in [
            "",
            "\n\n",
            META,
            r#"{"meta":{"format":{"version":"4.0.0"}}}"#,
            r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
        ] {
            agree(text.as_bytes(), 2, 8);
        }
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

    /// Every arena file: 4 workers, 4 KB chunks, same outcome as the sequential loader.
    #[test]
    fn arena_files_agree_with_sequential() {
        let root = Path::new("/home/user/Palladium/arena-tests");
        if !root.is_dir() {
            return;
        }
        let mut files = Vec::new();
        collect(&root.join("good"), &mut files);
        collect(&root.join("bad"), &mut files);
        for f in &files {
            let bytes = fs::read(f).expect("read");
            agree(&bytes, 4, 4096);
        }
    }
}

//! Parallel export loader. `load_parallel_stream` returns exactly what
//! `parse::load` returns for the reader's bytes, using worker threads.
//!
//! The input is read in pieces of about `CHUNK_BYTES`, each ending at a newline,
//! and handed to the workers through a bounded queue, so only a few pieces of
//! the file are in memory at any time (a worker frees its piece when it has
//! parsed it). Each chunk runs the same line grammar as the sequential loader
//! (`parse::item_line`) with the `Chunk` sink, which records raw records and
//! checks references under the assumption that the file is *dense*: the items
//! of each index namespace carry consecutive indices, and a reference is valid
//! when it names an item defined earlier.
//!
//! Names are interned by one thread while the workers parse, in file order
//! (their canonical ids must equal their file indices, so every name must be
//! new). Another thread merges the remaining records, also in file order and
//! while the workers parse: it checks the density across chunks, remaps the
//! chunk-local string, nat and constant-level indices, and appends to the final
//! vectors, so a chunk's records are freed soon after it is parsed. A chunk
//! that finds anything else (a reference
//! it cannot resolve locally, an error, an `mdata` alias, a duplicate name or
//! constant) makes the whole parallel attempt fail, and the result is the
//! sequential load of the same input, read again from its start. The outcome
//! (Ok, Reject or Decline, with the same message) is therefore the sequential
//! one by construction.

use std::collections::{BTreeMap, HashMap};
use std::io::{self, Read, Seek, SeekFrom};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

use crate::bignat::BigNat;
use crate::env::*;
use crate::parse::{item_line, lines, load_stream, meta_line, reject, trim, LResult, LoadError, Ns, Sink};

/// Default chunk size in bytes.
pub const CHUNK_BYTES: usize = 16 << 20;

/// Chunks that may wait in the queue between the reader and the workers.
const QUEUE_CHUNKS: usize = 1;

/// Loads an export held in memory with `threads` workers. Same result as `parse::load`.
pub fn load_parallel(bytes: &[u8], threads: usize) -> Result<Env, LoadError> {
    load_parallel_with(bytes, threads, CHUNK_BYTES)
}

/// `load_parallel` with an explicit chunk size (tests use tiny chunks).
pub fn load_parallel_with(bytes: &[u8], threads: usize, chunk_bytes: usize) -> Result<Env, LoadError> {
    match load_parallel_stream_with(&mut io::Cursor::new(bytes), threads, chunk_bytes) {
        Ok(r) => r,
        // A slice cannot fail to read or seek.
        Err(_) => crate::parse::load(bytes),
    }
}

/// Loads an export from a seekable reader with `threads` workers, without holding
/// the whole input in memory. Same result as `parse::load` of the reader's bytes.
/// `Err` is a read or seek error.
pub fn load_parallel_stream<R: Read + Seek>(src: &mut R, threads: usize) -> io::Result<Result<Env, LoadError>> {
    load_parallel_stream_with(src, threads, CHUNK_BYTES)
}

/// `load_parallel_stream` with an explicit chunk size.
pub fn load_parallel_stream_with<R: Read + Seek>(
    src: &mut R,
    threads: usize,
    chunk_bytes: usize,
) -> io::Result<Result<Env, LoadError>> {
    let len = src.seek(SeekFrom::End(0))?;
    src.seek(SeekFrom::Start(0))?;
    let hint = usize::try_from(len).unwrap_or(usize::MAX);
    if let Some(env) = try_parallel(src, threads.max(1), chunk_bytes.max(1), hint)? {
        return Ok(Ok(env));
    }
    if std::env::var_os("PALLADIUM_TRACE").is_some() {
        eprintln!("trace: parallel load fell back to the sequential loader");
    }
    src.seek(SeekFrom::Start(0))?;
    load_stream(src)
}

/// Parallel attempt. `Ok(None)` means "use the sequential loader".
fn try_parallel<R: Read>(src: &mut R, threads: usize, chunk_bytes: usize, len_hint: usize) -> io::Result<Option<Env>> {
    let trace = std::env::var_os("PALLADIUM_TRACE").is_some();
    let t0 = std::time::Instant::now();
    let Some((merger, names, count)) = parse_all(src, threads, chunk_bytes, len_hint)? else {
        return Ok(None);
    };
    let t1 = t0.elapsed();
    let env = merger.finish(names);
    if trace {
        eprintln!(
            "trace: parallel: {} chunks, read, parse, names and merge {:.3}s, finish {:.3}s",
            count,
            t1.as_secs_f64(),
            (t0.elapsed() - t1).as_secs_f64()
        );
    }
    Ok(Some(env))
}

/// Cuts a reader into pieces of about `chunk_bytes`, each ending just after a
/// newline (or at the end of the input).
struct Chunker<'a, R> {
    src: &'a mut R,
    chunk_bytes: usize,
    /// Bytes read past the end of the previous piece.
    carry: Vec<u8>,
    eof: bool,
}

impl<R: Read> Chunker<'_, R> {
    /// The next piece, built in `buf` (a recycled buffer). `None` at the end of the input.
    fn next(&mut self, mut buf: Vec<u8>) -> io::Result<Option<Vec<u8>>> {
        buf.clear();
        buf.extend_from_slice(&self.carry);
        self.carry.clear();
        // A newline in `buf[..scanned]` was already looked for.
        let mut scanned = 0usize;
        loop {
            if !self.eof && buf.len() < self.chunk_bytes {
                let want = self.chunk_bytes - buf.len();
                let old = buf.len();
                buf.resize(old + want, 0);
                let mut got = 0usize;
                while got < want {
                    match self.src.read(&mut buf[old + got..]) {
                        Ok(0) => {
                            self.eof = true;
                            break;
                        }
                        Ok(n) => got += n,
                        Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                        Err(e) => return Err(e),
                    }
                }
                buf.truncate(old + got);
            }
            if self.eof {
                return Ok((!buf.is_empty()).then_some(buf));
            }
            if let Some(p) = buf[scanned..].iter().rposition(|&b| b == b'\n') {
                let cut = scanned + p + 1;
                self.carry.extend_from_slice(&buf[cut..]);
                buf.truncate(cut);
                return Ok(Some(buf));
            }
            // One line longer than the piece: keep reading until it ends.
            scanned = buf.len();
            let more = self.chunk_bytes.max(4096);
            let old = buf.len();
            buf.resize(old + more, 0);
            let n = loop {
                match self.src.read(&mut buf[old..]) {
                    Ok(n) => break n,
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(e) => return Err(e),
                }
            };
            buf.truncate(old + n);
            if n == 0 {
                self.eof = true;
            }
        }
    }
}

/// Names of one chunk: prefixes, payloads and the bytes they point into.
type NameBatch = (usize, Vec<WName>, Vec<u8>);

/// A piece of the file for a worker: its position in file order, its bytes, and
/// where its item lines start (after the meta line in the first piece).
type Job = (usize, Vec<u8>, usize);

/// Reads the input piece by piece on the calling thread and parses the pieces on
/// `threads` workers, while one further thread interns the names and another
/// merges the other records, both in file order. Returns the merged records, the
/// name table and the number of chunks. `Ok(None)` if the meta line is missing or
/// not accepted, any chunk fails or does not continue the ones before it, a
/// thread panics, or the names are not fresh.
fn parse_all<R: Read>(src: &mut R, threads: usize, chunk_bytes: usize, len_hint: usize) -> io::Result<Option<(Merger, RawEnv, usize)>> {
    let failed = AtomicBool::new(false);
    let (name_tx, name_rx) = mpsc::channel::<NameBatch>();
    let (chunk_tx, chunk_rx) = mpsc::channel::<(usize, Chunk)>();
    let (job_tx, job_rx) = mpsc::sync_channel::<Job>(QUEUE_CHUNKS);
    let job_rx = Arc::new(Mutex::new(job_rx));
    // Parsed pieces' buffers go back to the reader.
    let (buf_tx, buf_rx) = mpsc::channel::<Vec<u8>>();
    let mut chunker = Chunker { src, chunk_bytes, carry: Vec::new(), eof: false };
    let (read, workers_ok, names, merged) = thread::scope(|s| {
        let names_thread = s.spawn(move || intern_stream(name_rx, len_hint));
        let failed_ref = &failed;
        let merge_thread = s.spawn(move || merge_stream(chunk_rx, failed_ref));
        let handles: Vec<_> = (0..threads)
            .map(|_| {
                let name_tx = name_tx.clone();
                let chunk_tx = chunk_tx.clone();
                let job_rx = Arc::clone(&job_rx);
                let buf_tx = buf_tx.clone();
                let failed = &failed;
                s.spawn(move || {
                    loop {
                        if failed.load(Ordering::Relaxed) {
                            break;
                        }
                        let job = match job_rx.lock() {
                            Ok(rx) => rx.recv(),
                            Err(_) => {
                                failed.store(true, Ordering::Relaxed);
                                return false;
                            }
                        };
                        let Ok((i, bytes, start)) = job else { break };
                        match parse_chunk(&bytes[start..]) {
                            Ok(mut c) => {
                                let _ = buf_tx.send(bytes);
                                let names = std::mem::take(&mut c.names);
                                let buf = std::mem::take(&mut c.names_buf);
                                let _ = name_tx.send((i, names, buf));
                                let _ = chunk_tx.send((i, c));
                            }
                            Err(_) => {
                                failed.store(true, Ordering::Relaxed);
                                return false;
                            }
                        }
                    }
                    true
                })
            })
            .collect();
        drop((name_tx, chunk_tx, job_rx, buf_tx));
        // `Ok(Some(n))`: `n` pieces were sent. `Ok(None)`: the parallel attempt is off.
        let read = (|| -> io::Result<Option<usize>> {
            let mut sent = 0usize;
            let mut have_meta = false;
            loop {
                if failed.load(Ordering::Relaxed) {
                    return Ok(None);
                }
                let Some(bytes) = chunker.next(buf_rx.try_recv().unwrap_or_default())? else {
                    return Ok(have_meta.then_some(sent));
                };
                let mut start = 0usize;
                if !have_meta {
                    // The meta line is the first non-empty line; the sequential loader checks it.
                    let mut pos = 0usize;
                    for l in lines(&bytes) {
                        pos += l.len() + 1;
                        let l = trim(l);
                        if !l.is_empty() {
                            if meta_line(l).is_err() {
                                return Ok(None);
                            }
                            have_meta = true;
                            break;
                        }
                    }
                    if !have_meta {
                        continue;
                    }
                    start = pos.min(bytes.len());
                }
                // Fails only when every worker has stopped.
                if job_tx.send((sent, bytes, start)).is_err() {
                    return Ok(None);
                }
                sent += 1;
            }
        })();
        if !matches!(read, Ok(Some(_))) {
            failed.store(true, Ordering::Relaxed);
        }
        drop(job_tx);
        let workers_ok = handles.into_iter().fold(true, |ok, h| h.join().unwrap_or(false) && ok);
        (read, workers_ok, names_thread.join().ok().flatten(), merge_thread.join().ok().flatten())
    });
    let Some(total) = read? else {
        return Ok(None);
    };
    if !workers_ok || failed.load(Ordering::Relaxed) {
        return Ok(None);
    }
    let (Some((names, interned)), Some((merger, merged))) = (names, merged) else {
        return Ok(None);
    };
    Ok((interned == total && merged == total).then_some((merger, names, total)))
}

/// Interns name batches in file order as they arrive. Returns the name table and
/// the number of batches interned (consecutive from the first), or `None` when
/// some name was not new with the expected id.
fn intern_stream(rx: mpsc::Receiver<NameBatch>, file_len: usize) -> Option<(RawEnv, usize)> {
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
    ok.then_some((env, next))
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

/// Builds the final vectors from the chunks, taken in file order: checks the density
/// across chunks and remaps the chunk-local string, nat and constant-level indices.
/// Each chunk's records are freed as soon as they are appended.
struct Merger {
    /// Everything but the names, which the interning thread builds.
    out: RawEnv,
    consts: Vec<Option<ConstInfo>>,
    str_ix: HashMap<String, u32>,
    /// Next file index per namespace.
    base: [u64; 3],
}

impl Merger {
    fn new() -> Self {
        // Names and levels start after the predefined 0 (`RawEnv::new` holds level 0).
        Merger { out: RawEnv::new(), consts: Vec::new(), str_ix: HashMap::new(), base: [1, 1, 0] }
    }

    /// Appends the next chunk in file order. `None` means the file needs the sequential loader.
    fn add(&mut self, ch: Chunk) -> Option<()> {
        let Chunk { ns, levels, exprs, nats, strs, const_levels, decls, consts: cs, .. } = ch;
        let env = &mut self.out;
        for k in 0..3 {
            let st = ns[k];
            if st.first.is_some_and(|f| f != self.base[k]) {
                return None;
            }
            if st.pre_max.is_some_and(|p| p >= self.base[k]) {
                return None;
            }
        }
        for k in 0..3 {
            self.base[k] += ns[k].count;
        }
        let mut smap = Vec::with_capacity(strs.len());
        for s in strs {
            let i = match self.str_ix.get(&s) {
                Some(&i) => i,
                None => {
                    let i = u32::try_from(env.strs.len()).ok()?;
                    env.strs.push(s.clone());
                    self.str_ix.insert(s, i);
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
            if self.consts.len() <= i {
                self.consts.resize_with(i + 1, || None);
            }
            if self.consts[i].is_some() {
                return None;
            }
            self.consts[i] = Some(info);
        }
        env.levels.extend_from_slice(&levels);
        env.exprs.reserve(exprs.len());
        for mut n in exprs {
            match n.tag {
                RawTag::Const => n.b = n.b.checked_add(cl_base)?,
                RawTag::Nat => n.a = n.a.checked_add(nat_base)?,
                RawTag::Str => n.a = *smap.get(n.a as usize)?,
                _ => {}
            }
            env.exprs.push(n);
        }
        Some(())
    }

    /// The environment, with the name table of the interning thread.
    fn finish(self, mut names: RawEnv) -> Env {
        let Merger { out, mut consts, .. } = self;
        let RawEnv { levels, mut exprs, const_levels, nats, strs, decls, .. } = out;
        exprs.shrink_to_fit();
        names.levels = levels;
        names.exprs = exprs;
        names.const_levels = const_levels;
        names.nats = nats;
        names.strs = strs;
        names.decls = decls;
        if consts.len() < names.names.len() {
            consts.resize_with(names.names.len(), || None);
        }
        let builtins = Builtins::resolve(&names);
        Env { raw: names, consts, builtins }
    }
}

/// Merges parsed chunks in file order as they arrive. Returns the merger and the
/// number of chunks merged (consecutive from the first), or `None` (and sets
/// `failed`) when a chunk does not continue the ones before it.
fn merge_stream(rx: mpsc::Receiver<(usize, Chunk)>, failed: &AtomicBool) -> Option<(Merger, usize)> {
    let mut merger = Merger::new();
    let mut pending: BTreeMap<usize, Chunk> = BTreeMap::new();
    let mut next = 0usize;
    let mut ok = true;
    for (i, ch) in rx {
        if !ok {
            // Keep receiving so that no worker's records pile up.
            continue;
        }
        pending.insert(i, ch);
        while let Some(ch) = pending.remove(&next) {
            if merger.add(ch).is_none() {
                ok = false;
                failed.store(true, Ordering::Relaxed);
                pending.clear();
                break;
            }
            next += 1;
        }
    }
    ok.then_some((merger, next))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::load;
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
        matches!(try_parallel(&mut io::Cursor::new(bytes), 2, chunk, bytes.len()), Ok(Some(_)))
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

    /// A reader that returns at most `step` bytes per call, and fails after `fail_at` bytes.
    struct Slow<'a> {
        inner: io::Cursor<&'a [u8]>,
        step: usize,
        fail_at: Option<u64>,
    }

    impl Read for Slow<'_> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.fail_at.is_some_and(|f| self.inner.position() >= f) {
                return Err(io::Error::other("read failed"));
            }
            let n = buf.len().min(self.step);
            self.inner.read(&mut buf[..n])
        }
    }

    impl Seek for Slow<'_> {
        fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
            self.inner.seek(pos)
        }
    }

    /// Short reads, long lines against small chunks, and fallbacks that read the input again.
    #[test]
    fn short_reads_agree() {
        let mut texts = vec![file(DENSE), file(DENSE) + "\n", String::new()];
        // Falls back (sparse index): the second pass starts from the first byte again.
        texts.push(file(&[r#"{"ie":0,"sort":0}"#, r#"{"ie":5,"sort":0}"#, r#"{"ie":6,"app":{"fn":5,"arg":0}}"#]));
        texts.push(file(&[r#"{"ie":0,"sort":0}"#, r#"{"ie":1,"sort":"#]));
        for text in &texts {
            let bytes = text.as_bytes();
            let seq = load(bytes);
            for (step, chunk) in [(1usize, 1usize), (3, 7), (5, 64), (1000, 50), (7, 1 << 20)] {
                let mut src = Slow { inner: io::Cursor::new(bytes), step, fail_at: None };
                let par = load_parallel_stream_with(&mut src, 3, chunk).expect("no read error");
                match (&seq, &par) {
                    (Ok(a), Ok(b)) => assert!(same_env(a, b), "envs differ (step {step}, chunk {chunk})"),
                    (Err(a), Err(b)) => assert_eq!(a, b),
                    _ => panic!("outcomes differ (step {step}, chunk {chunk})"),
                }
            }
        }
    }

    #[test]
    fn read_errors_are_reported() {
        let text = file(DENSE);
        let bytes = text.as_bytes();
        for fail_at in [0u64, 10, 200, bytes.len() as u64 - 1] {
            for chunk in [1usize, 64, 1 << 20] {
                let mut src = Slow { inner: io::Cursor::new(bytes), step: 16, fail_at: Some(fail_at) };
                assert!(load_parallel_stream_with(&mut src, 2, chunk).is_err(), "fail_at {fail_at}, chunk {chunk}");
            }
        }
    }

    /// `PALLADIUM_BIG_EXPORT=<file> cargo test --release -- --ignored big_export`: the
    /// streamed parallel load of a large export equals its streamed sequential load.
    /// Holds both environments in memory.
    #[test]
    #[ignore]
    fn big_export_agrees_with_sequential() {
        let Some(path) = std::env::var_os("PALLADIUM_BIG_EXPORT") else { return };
        let mut f = fs::File::open(&path).expect("open");
        let par = load_parallel_stream(&mut f, 4).expect("read").expect("parallel load");
        let mut f = fs::File::open(&path).expect("open");
        let seq = load_stream(&mut f).expect("read").expect("sequential load");
        assert!(same_env(&seq, &par));
    }
}

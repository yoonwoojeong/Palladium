//! `palladium [-j N] [-q] <file | ->`: checks an export file (docs/DESIGN.md section 7).
//! Exit codes: 0 valid, 1 rejected, 2 declined, 3 faults (resource limit / internal), 4 I/O or setup error.

use std::io::Read;
use std::panic::{self, AssertUnwindSafe};
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::thread;

use palladium::env::{Decl, Env, NameId};
use palladium::parse::{self, LoadError};
use palladium::parse_par;
use palladium::tc::{Checker, Fail};

const STACK_SIZES: [usize; 3] = [4 << 30, 1 << 30, 256 << 20];
/// A worker recreates its store between declarations once it holds more terms than this.
const RESET_TERMS: usize = 3_000_000;

struct Opts {
    jobs: Option<usize>,
    quiet: bool,
    parse_only: bool,
    /// Uses the sequential reference loader (for benchmarks).
    sequential: bool,
    input: String,
}

fn usage() -> ! {
    eprintln!("usage: palladium [-j N] [-q] [--parse-only] <file | ->");
    process::exit(4)
}

fn parse_args() -> Opts {
    let mut opts = Opts { jobs: None, quiet: false, parse_only: false, sequential: false, input: String::new() };
    let mut args = std::env::args().skip(1);
    let mut have_input = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "-q" => opts.quiet = true,
            "--parse-only" => opts.parse_only = true,
            "--sequential" => opts.sequential = true,
            "-j" => match args.next().and_then(|n| n.parse::<usize>().ok()) {
                Some(n) if n >= 1 => opts.jobs = Some(n),
                _ => usage(),
            },
            "-h" | "--help" => usage(),
            _ if a.starts_with('-') && a != "-" => usage(),
            _ => {
                if have_input {
                    usage();
                }
                opts.input = a;
                have_input = true;
            }
        }
    }
    if !have_input {
        usage();
    }
    opts
}

fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panic".to_string()
    }
}

fn decl_name(env: &Env, pos: usize) -> String {
    let name: Option<NameId> = match env.raw.decls.get(pos) {
        Some(Decl::Axiom { name }) | Some(Decl::Def { name }) | Some(Decl::Thm { name }) | Some(Decl::Opaque { name }) | Some(Decl::Quot { name }) => Some(*name),
        Some(Decl::Inductive { types, .. }) => types.first().copied(),
        None => None,
    };
    match name {
        Some(n) => env.raw.name_to_string(n),
        None => format!("#{pos}"),
    }
}

/// Checks declarations until the shared counter is exhausted.
fn worker(env: &Env, counter: &AtomicUsize, fault: &Mutex<Option<String>>, total: usize) {
    let trace = std::env::var_os("PALLADIUM_TRACE").is_some();
    let mut checker = Checker::new(env);
    loop {
        let p = counter.fetch_add(1, Ordering::Relaxed);
        if p >= total {
            break;
        }
        if checker.store.num_terms() > RESET_TERMS {
            checker.reset();
        }
        let t0 = trace.then(std::time::Instant::now);
        if trace {
            eprintln!("start: {} {}", p, decl_name(env, p));
            if let Decl::Def { name } = &env.raw.decls[p] {
                if let Some(info) = env.get(*name) {
                    if let palladium::env::ConstKind::Def { value, .. } = info.kind {
                        let v = checker.import_expr(value);
                        eprintln!("value: {}", checker.show(v).chars().take(1500).collect::<String>());
                    }
                }
            }
        }
        let res = panic::catch_unwind(AssertUnwindSafe(|| checker.check_decl(p as u32)));
        if let Some(t0) = t0 {
            eprintln!("trace: {} {:.1}ms terms={} stats(infer,wcore,whnf,defeq,rec,rule)={:?}", decl_name(env, p), t0.elapsed().as_secs_f64() * 1e3, checker.store.num_terms(), checker.stats);
        }
        let msg = match res {
            Ok(Ok(())) => continue,
            Ok(Err(Fail::Reject(msg))) => {
                eprintln!("rejected: {}: {}", decl_name(env, p), msg);
                process::exit(1)
            }
            Ok(Err(Fail::Fault(msg))) => format!("{}: {}", decl_name(env, p), msg),
            Err(payload) => format!("{}: panic: {}", decl_name(env, p), panic_message(&*payload)),
        };
        if let Ok(mut f) = fault.lock() {
            if f.is_none() {
                *f = Some(msg);
            }
        }
        checker = Checker::new(env);
    }
}

/// Peak resident set size (VmHWM) in KiB, or 0 when unavailable.
fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find_map(|l| l.strip_prefix("VmHWM:"))
                .and_then(|v| v.trim().trim_end_matches("kB").trim().parse::<u64>().ok())
        })
        .unwrap_or(0)
}

fn main() {
    panic::set_hook(Box::new(|_| {}));
    let opts = parse_args();
    let trace = std::env::var_os("PALLADIUM_TRACE").is_some();
    let t_read = std::time::Instant::now();
    let bytes = if opts.input == "-" {
        let mut v = Vec::new();
        if let Err(e) = std::io::stdin().read_to_end(&mut v) {
            eprintln!("error: reading stdin: {e}");
            process::exit(4);
        }
        v
    } else {
        match std::fs::read(&opts.input) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("error: reading {}: {e}", opts.input);
                process::exit(4);
            }
        }
    };
    let jobs = opts
        .jobs
        .unwrap_or_else(|| thread::available_parallelism().map(|n| n.get()).unwrap_or(1).min(8))
        .max(1);
    if trace {
        eprintln!("trace: read {:.3}s, {} bytes", t_read.elapsed().as_secs_f64(), bytes.len());
    }
    let t_parse = std::time::Instant::now();
    let loaded = if opts.sequential {
        parse::load(&bytes)
    } else {
        parse_par::load_parallel(&bytes, jobs)
    };
    if trace {
        let mode = if opts.sequential { "sequential".to_string() } else { format!("{jobs} threads") };
        eprintln!("trace: parse and env build {:.3}s ({mode})", t_parse.elapsed().as_secs_f64());
    }
    let env = match loaded {
        Ok(e) => e,
        Err(LoadError::Reject(m)) => {
            eprintln!("rejected: {m}");
            process::exit(1);
        }
        Err(LoadError::Decline(m)) => {
            eprintln!("declined: {m}");
            process::exit(2);
        }
    };
    // The file bytes are not needed past this point.
    drop(bytes);
    if trace {
        eprintln!("trace: peak RSS after load {}", peak_rss_kib());
    }
    if opts.parse_only {
        if !opts.quiet {
            println!("parsed: {} declarations, {} exprs", env.raw.decls.len(), env.raw.exprs.len());
        }
        process::exit(0);
    }
    let total = env.raw.decls.len();
    let t_check = std::time::Instant::now();
    let counter = AtomicUsize::new(0);
    let fault: Mutex<Option<String>> = Mutex::new(None);
    let env_ref = &env;
    let counter_ref = &counter;
    let fault_ref = &fault;
    thread::scope(|s| {
        for _ in 0..jobs {
            let mut spawned = false;
            for &size in &STACK_SIZES {
                if thread::Builder::new()
                    .stack_size(size)
                    .spawn_scoped(s, move || worker(env_ref, counter_ref, fault_ref, total))
                    .is_ok()
                {
                    spawned = true;
                    break;
                }
            }
            if !spawned {
                eprintln!("error: cannot spawn a worker thread");
                process::exit(4);
            }
        }
    });
    if let Some(msg) = fault.into_inner().ok().flatten() {
        eprintln!("fault: {msg}");
        process::exit(3);
    }
    if trace {
        eprintln!("trace: check {:.3}s, peak RSS {} KiB", t_check.elapsed().as_secs_f64(), peak_rss_kib());
    }
    if !opts.quiet {
        println!("ok: {total} declarations");
    }
    process::exit(0);
}

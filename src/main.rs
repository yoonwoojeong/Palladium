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
const RESET_TERMS: usize = 250_000;

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

/// Per-thread accounting (`PALLADIUM_STATS=1`): printed once per worker at the end, so that
/// measuring does not serialise the threads.
#[derive(Default)]
struct WStats {
    decls: u64,
    check_ns: u64,
    reset_ns: u64,
    resets: u64,
    resets_terms: u64,
    dbg_ns: u64,
    loop_ns: u64,
    imported: u64,
}

/// Process-wide (utime+stime in clock ticks, minflt, majflt) from /proc/self/stat, and this
/// thread's (voluntary, involuntary) context switches from /proc/thread-self/status.
fn thread_usage() -> (u64, u64, u64, u64, u64) {
    let proc_stat = std::fs::read_to_string("/proc/self/stat").unwrap_or_default();
    let rest = proc_stat.rsplit(')').next().unwrap_or("");
    // Tokens after the comm: index 0 is the state (field 3), so minflt(10)=7, majflt(12)=9, utime(14)=11, stime(15)=12.
    let f: Vec<u64> = rest.split_whitespace().skip(1).map(|x| x.parse().unwrap_or(0)).collect();
    let g = |i: usize| f.get(i).copied().unwrap_or(0);
    let status = std::fs::read_to_string("/proc/thread-self/status").unwrap_or_default();
    let cs = |key: &str| {
        status
            .lines()
            .find_map(|l| l.strip_prefix(key))
            .and_then(|v| v.trim().parse::<u64>().ok())
            .unwrap_or(0)
    };
    (g(10) + g(11), g(6), g(8), cs("voluntary_ctxt_switches:"), cs("nonvoluntary_ctxt_switches:"))
}

/// Checks declarations until the shared counter is exhausted.
fn worker(env: &Env, counter: &AtomicUsize, fault: &Mutex<Option<String>>, total: usize) {
    let trace = std::env::var_os("PALLADIUM_TRACE").is_some();
    let stats_on = std::env::var_os("PALLADIUM_STATS").is_some();
    let only_pos: Option<usize> = std::env::var("PALLADIUM_ONLY_POS").ok().and_then(|v| v.parse().ok());
    // Diagnostics: `PALLADIUM_RESET_TERMS=<n>` overrides the store size that triggers a reset.
    let reset_terms: usize = std::env::var("PALLADIUM_RESET_TERMS").ok().and_then(|v| v.parse().ok()).unwrap_or(RESET_TERMS);
    let t_loop = std::time::Instant::now();
    let u0 = thread_usage();
    let mut ws = WStats::default();
    let mut checker = Checker::new(env);
    loop {
        let p = counter.fetch_add(1, Ordering::Relaxed);
        if p >= total {
            break;
        }
        // Diagnostics only: `PALLADIUM_ONLY_POS=<n>` checks just declaration n (the environment
        // still holds all declarations, so n is checked as it would be in the full run).
        if only_pos.map_or(false, |o| o != p) {
            continue;
        }
        if checker.store.num_terms() > reset_terms {
            let tr = std::time::Instant::now();
            ws.resets_terms += checker.store.num_terms() as u64;
            checker.reset();
            ws.reset_ns += tr.elapsed().as_nanos() as u64;
            ws.resets += 1;
        }
        ws.decls += 1;
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
        let tc0 = std::time::Instant::now();
        let res = panic::catch_unwind(AssertUnwindSafe(|| checker.check_decl(p as u32)));
        ws.check_ns += tc0.elapsed().as_nanos() as u64;
        if trace {
            let td = std::time::Instant::now();
            checker.dump_dbg();
            ws.dbg_ns += td.elapsed().as_nanos() as u64;
        }
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
        let tr = std::time::Instant::now();
        checker = Checker::new(env);
        ws.reset_ns += tr.elapsed().as_nanos() as u64;
    }
    if stats_on {
        ws.loop_ns = t_loop.elapsed().as_nanos() as u64;
        ws.imported = checker.imported_nodes();
        let u1 = thread_usage();
        eprintln!(
            "stats: thread decls={} check={:.2}s reset={:.2}s resets={} avg_terms_at_reset={} loop={:.2}s dbg={:.2}s imported_nodes={} process_cpu_so_far={:.2}s process_minflt={} process_majflt={} thread_vcs={} thread_ivcs={}",
            ws.decls,
            ws.check_ns as f64 / 1e9,
            ws.reset_ns as f64 / 1e9,
            ws.resets,
            ws.resets_terms / ws.resets.max(1),
            ws.loop_ns as f64 / 1e9,
            ws.dbg_ns as f64 / 1e9,
            ws.imported,
            u1.0 as f64 / 100.0,
            u1.1 - u0.1,
            u1.2 - u0.2,
            u1.3 - u0.3,
            u1.4 - u0.4
        );
    }
}

/// Peak resident set size (VmHWM) in KiB, or 0 when unavailable.
fn peak_rss_kib() -> u64 {
    rss_field("VmHWM:")
}

/// Current resident set size (VmRSS) in KiB, or 0 when unavailable.
fn current_rss_kib() -> u64 {
    rss_field("VmRSS:")
}

fn rss_field(key: &str) -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find_map(|l| l.strip_prefix(key))
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
        eprintln!("trace: peak RSS after load {} KiB, current RSS {} KiB", peak_rss_kib(), current_rss_kib());
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
    // A partial (diagnostic) run must never be reported as an acceptance of the file.
    if std::env::var_os("PALLADIUM_ONLY_POS").is_some() {
        eprintln!("PALLADIUM_ONLY_POS set: only one declaration was checked; declining");
        process::exit(2);
    }
    if !opts.quiet {
        println!("ok: {total} declarations");
    }
    process::exit(0);
}

# Palladium

An independent Lean 4 kernel (type checker) written from scratch in Rust with **zero
dependencies**, built for the [Lean Kernel Arena](https://arena.lean-lang.org).

```
cargo build --release
target/release/palladium [-j N] [-q] <export.ndjson | ->
```
Exit code: `0` accepted, `1` rejected, `2` declined, other = internal error.
Input is the NDJSON format of [`lean4export`](https://github.com/leanprover/lean4export) (v3.x).

## Design in one paragraph

Terms are hash-consed with binder names erased, so alpha-equivalence is integer equality.
Binders are opened with *canonical typed locals* — a local is the pair (depth, type) — so a
term carries its own typing context and every cache (inference, weak head normal form,
definitional equality, including failures) is context-free and never invalidated. Type
inference runs under an environment and never substitutes into binder bodies. Universe
levels are compared with a complete decision procedure. Declarations are checked in
parallel under a file-order dependency rule, and nothing in the export is trusted:
recursors, their computation rules and all inductive metadata are re-derived and compared.
See `docs/DESIGN.md`, `docs/CHECKER.md`, `docs/EVAL.md`.

## Testing

```
scripts/fetch-arena-tests.sh                 # downloads the arena's small tests
python3 scripts/run-arena.py -P 2            # expects good: all ok, bad: all ok
cargo test --release
```
`scripts/build-pgo.sh <export.ndjson>` builds with profile-guided optimisation (about 10%
faster on Mathlib than a plain build of the same source; it falls back to a plain build
when no matching `llvm-profdata` is found, `rustup component add llvm-tools` provides one).

Debug switches: `PALLADIUM_TRACE=1` (per-declaration timings), `PALLADIUM_STATS=1` (phase
times, RSS and per-thread accounting only), `PALLADIUM_SAMPLE=<k>` (checks every k-th
declaration for quick timing comparisons, and declines), `PALLADIUM_CHECK_INFER=1`
(cross-check environment-based inference against the substitution-based one).

## Status

Passes the arena's downloadable suite (all valid files accepted, all invalid files
rejected) and accepts the `Init` (58k declarations, ~4 s) and `Std` (98k declarations, ~7 s)
exports of Lean 4.34.1 on 4 threads, and all of Mathlib v4.34.1 (702,040 declarations,
104.9M expressions, 6.18 GB export). Mathlib on 4 threads of a 4-core 2.1 GHz Xeon, with the
profile-guided build below: load 3.2 s (peak 2.8 GB, the file is parsed as it is read and
never held whole), check 129 s, peak 4.1 GB. A plain `cargo build --release` checks it in
142–148 s. An export on stdin is read whole unless `--sequential` is given.

Checking time is spread flat over Mathlib: the 100 slowest declarations hold 4% of it, the
1000 slowest 12%, and the slowest single one takes 3 s. About a third of it is hash-consing
lookups, from substitution, beta reduction and importing terms. Reduction-heavy proofs
(`decide` over large search spaces) are slow compared with environment-machine kernels.

## Arena checker definition

```yaml
description: |
  Palladium: a dependency-free Rust kernel with hash-consed, name-erased terms,
  canonical typed locals (context-free caches) and parallel declaration checking.
url: https://github.com/yoonwoojeong/Palladium
ref: main
rev: <commit>
build: |
  ROOT=$(cd ../../../.. && pwd)
  "$ROOT/lka.py" build-test init-prelude
  scripts/build-pgo.sh "$ROOT/_build/tests/init-prelude.ndjson"
run: target/release/palladium -q -j 4 "$IN"
threads: 4
```

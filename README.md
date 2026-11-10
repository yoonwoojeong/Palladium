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
Debug switches: `PALLADIUM_TRACE=1` (per-declaration timings), `PALLADIUM_CHECK_INFER=1`
(cross-check environment-based inference against the substitution-based one).

## Status

Passes the arena's downloadable suite (all valid files accepted, all invalid files
rejected). Not yet run against the large corpora (`Init`, `Std`, Mathlib).

## Arena checker definition

```yaml
description: |
  Palladium: a dependency-free Rust kernel with hash-consed, name-erased terms,
  canonical typed locals (context-free caches) and parallel declaration checking.
url: https://github.com/yoonwoojeong/Palladium
ref: main
rev: <commit>
build: RUSTFLAGS="-C target-cpu=native" cargo build --release
run: target/release/palladium -q -j 4 "$IN"
threads: 4
```

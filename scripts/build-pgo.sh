#!/bin/sh
# Builds target/release/palladium with profile-guided optimisation.
#
# Usage: scripts/build-pgo.sh EXPORT.ndjson
#
# EXPORT is a valid export to profile on (the arena's init-prelude is enough: a profile from
# it and one from all of Init give the same speed-up on Mathlib, about 10%). The script
# builds an instrumented binary, checks EXPORT with it, and rebuilds with the profile.
# RUSTFLAGS from the environment are kept. If no llvm-profdata matching rustc is found, or
# any profiling step fails, it falls back to a plain release build, so the result is always
# target/release/palladium.
set -eu
cd "$(dirname "$0")/.."
IN=$1
BASE_FLAGS=${RUSTFLAGS:-}
DIR=$PWD/target/pgo

plain() {
    echo "build-pgo: $1; building without a profile" >&2
    RUSTFLAGS="$BASE_FLAGS" cargo build --release
    exit 0
}

# rustup's llvm-tools component matches rustc; a system llvm-profdata may be too old.
PROFDATA=$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata 2>/dev/null | head -n 1 || true)
[ -n "$PROFDATA" ] || PROFDATA=$(command -v llvm-profdata || true)
[ -n "$PROFDATA" ] || plain "no llvm-profdata found (try: rustup component add llvm-tools)"

rm -rf "$DIR"
mkdir -p "$DIR"
RUSTFLAGS="$BASE_FLAGS -Cprofile-generate=$DIR/raw" cargo build --release --target-dir "$DIR/gen" \
    || plain "the instrumented build failed"
"$DIR/gen/release/palladium" -q -j 4 "$IN" || plain "the profiling run did not accept $IN"
"$PROFDATA" merge -o "$DIR/merged.profdata" "$DIR/raw" || plain "llvm-profdata could not merge the profile"
RUSTFLAGS="$BASE_FLAGS -Cprofile-use=$DIR/merged.profdata" cargo build --release \
    || plain "the profile-guided build failed"
rm -rf "$DIR/gen" "$DIR/raw"

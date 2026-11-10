#!/bin/sh
# Downloads the Lean Kernel Arena test suite (small tests) into ./arena-tests/{good,bad}
set -e
mkdir -p arena-tests && cd arena-tests
curl -sSfO https://arena.lean-lang.org/lean-arena-tests.tar.gz
tar xzf lean-arena-tests.tar.gz && rm lean-arena-tests.tar.gz

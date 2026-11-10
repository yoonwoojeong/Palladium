#!/usr/bin/env python3
"""Builds a large synthetic export by replicating an input export K times.

Usage: gen-big.py IN.ndjson K OUT.ndjson

The meta line is copied once. Copy 0 is the input unchanged. Copy j >= 1 is
shifted so that its indices continue the previous copy's: with M the largest
index used in the input for a namespace, copy j adds j*(M+1) to name indices
(0 stays 0), j*M to level indices (0 stays 0) and j*(M+1) to expression
indices. Every reference is shifted the same way. Each copy j >= 1 starts with
a fresh name `copyJ` (its index is the copy's base), and every name line of the
copy whose prefix is the anonymous name is re-rooted under it, so declared
names stay unique. The output keeps the dense, ascending index order of the
input, so it takes the parallel loader's fast path.

Caveat: builtin names such as `Nat` or `String` lose their builtin meaning in
copies j >= 1, so literals will not type-check there. Use this output for
parsing benchmarks; use an input without literals for checking benchmarks.
"""

import json
import sys

NAME_SCALAR = {"name", "pre", "typeName", "induct", "ctor", "param"}
LEVEL_SCALAR = {"succ", "sort"}
EXPR_SCALAR = {"fn", "arg", "type", "body", "value", "struct", "expr", "rhs"}
NAME_LIST = {"levelParams", "all", "ctors"}
LEVEL_LIST = {"us", "max", "imax"}


class Mapper:
    def __init__(self, off_n, off_l, off_e):
        self.off_n = off_n
        self.off_l = off_l
        self.off_e = off_e

    def name(self, i):
        return 0 if i == 0 else i + self.off_n

    def level(self, i):
        return 0 if i == 0 else i + self.off_l

    def expr(self, i):
        return i + self.off_e

    def value(self, v, key):
        if isinstance(v, dict):
            return {k: self.value(x, k) for k, x in v.items()}
        if isinstance(v, list):
            return [self.elem(x, key) for x in v]
        if isinstance(v, int) and not isinstance(v, bool):
            if key in NAME_SCALAR:
                return self.name(v)
            if key in LEVEL_SCALAR:
                return self.level(v)
            if key in EXPR_SCALAR:
                return self.expr(v)
        return v

    def elem(self, x, key):
        if isinstance(x, dict):
            return self.value(x, None)
        if isinstance(x, int) and not isinstance(x, bool):
            if key in NAME_LIST:
                return self.name(x)
            if key in LEVEL_LIST:
                return self.level(x)
        return x

    def line(self, obj, reroot):
        out = {}
        for k, v in obj.items():
            if k == "in":
                out[k] = self.name(v)
            elif k == "il":
                out[k] = self.level(v)
            elif k == "ie":
                out[k] = self.expr(v)
            else:
                out[k] = self.value(v, k)
        if reroot is not None and "in" in out:
            payload = out.get("str", out.get("num"))
            if isinstance(payload, dict) and payload.get("pre") == 0:
                payload["pre"] = reroot
        return out


def main():
    if len(sys.argv) != 4:
        print(__doc__, file=sys.stderr)
        sys.exit(4)
    src, k, dst = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    if k < 1:
        print("K must be at least 1", file=sys.stderr)
        sys.exit(4)
    with open(src, "rb") as f:
        lines = [l for l in f.read().split(b"\n") if l.strip()]
    meta, body = lines[0], lines[1:]
    parsed = [json.loads(l) for l in body]
    top = {"in": 0, "il": 0, "ie": 0}
    for obj in parsed:
        for key in top:
            if key in obj:
                top[key] = max(top[key], obj[key])
    m_n, m_l, m_e = top["in"], top["il"], top["ie"]
    with open(dst, "wb") as out:
        out.write(meta.strip() + b"\n")
        for j in range(k):
            off_n = j * (m_n + 1)
            mp = Mapper(off_n, j * m_l, j * (m_e + 1))
            if j >= 1:
                prefix = {"in": off_n, "str": {"pre": 0, "str": f"copy{j}"}}
                out.write(json.dumps(prefix, separators=(",", ":")).encode() + b"\n")
            for obj in parsed if j == 0 else [json.loads(l) for l in body]:
                reroot = off_n if j >= 1 else None
                line = mp.line(obj, reroot)
                out.write(json.dumps(line, separators=(",", ":")).encode() + b"\n")


if __name__ == "__main__":
    main()

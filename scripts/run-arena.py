#!/usr/bin/env python3
"""Runs target/release/palladium on the arena tests.

good/**/*.ndjson must exit 0, bad/**/*.ndjson must exit 1. Files under a `corner-cases`
directory accept either. Usage: run-arena.py [--tests DIR] [--timeout S] [-P N] [--bin PATH] [FILTER]
"""

import argparse
import concurrent.futures as cf
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def expected_ok(cat, rel, code):
    if "corner-cases" in rel.split(os.sep):
        return code in (0, 1)
    return code == (0 if cat == "good" else 1)


def run_one(binp, timeout, cat, rel, path):
    t0 = time.time()
    try:
        p = subprocess.run([binp, "-q", path], capture_output=True, timeout=timeout)
        code = p.returncode
        err = p.stderr.decode("utf-8", errors="replace")
    except subprocess.TimeoutExpired:
        code = None
        err = ""
    dt = time.time() - t0
    ok = code is not None and expected_ok(cat, rel, code)
    first = next((l for l in err.splitlines() if l.strip()), "")
    return {"cat": cat, "rel": rel, "code": code, "ok": ok, "time": dt, "err": first}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("filter", nargs="?", default="", help="substring of the relative test path")
    ap.add_argument("--tests", default=os.path.join(ROOT, "arena-tests"), help="arena tests directory")
    ap.add_argument("--timeout", type=float, default=60.0, help="per-file timeout in seconds")
    ap.add_argument("-P", type=int, default=4, help="parallel processes")
    ap.add_argument("--bin", default=os.path.join(ROOT, "target", "release", "palladium"))
    args = ap.parse_args()

    if not os.path.isfile(args.bin):
        print(f"binary not found: {args.bin} (run cargo build --release)", file=sys.stderr)
        return 2

    jobs = []
    for cat in ("good", "bad"):
        base = os.path.join(args.tests, cat)
        for dp, _dn, fn in os.walk(base):
            for f in fn:
                if not f.endswith(".ndjson"):
                    continue
                path = os.path.join(dp, f)
                rel = os.path.relpath(path, args.tests)
                if args.filter and args.filter not in rel:
                    continue
                jobs.append((cat, rel, path))
    jobs.sort(key=lambda j: j[1])

    start = time.time()
    results = []
    with cf.ThreadPoolExecutor(max_workers=max(1, args.P)) as ex:
        futs = [ex.submit(run_one, args.bin, args.timeout, *j) for j in jobs]
        for fu in cf.as_completed(futs):
            results.append(fu.result())
    wall = time.time() - start
    results.sort(key=lambda r: r["rel"])

    for r in results:
        if r["ok"]:
            continue
        if r["code"] is None:
            print(f"FAIL {r['rel']}: timeout after {args.timeout:g}s")
        else:
            print(f"FAIL {r['rel']}: exit {r['code']}: {r['err']}")

    def subdir(rel):
        parts = rel.split(os.sep)
        return os.sep.join(parts[:2]) if len(parts) > 2 else parts[0]

    totals = {}
    for r in results:
        for key in (r["cat"], subdir(r["rel"])):
            t = totals.setdefault(key, [0, 0])
            t[1] += 1
            if r["ok"]:
                t[0] += 1
    print()
    for cat in ("good", "bad"):
        if cat in totals:
            ok, n = totals[cat]
            print(f"{cat}: {ok}/{n} ok")
    for key in sorted(k for k in totals if k not in ("good", "bad")):
        ok, n = totals[key]
        print(f"  {key}: {ok}/{n} ok")

    slow = sorted((r for r in results if r["cat"] == "good" and r["code"] is not None), key=lambda r: -r["time"])[:5]
    if slow:
        print("slowest good: " + ", ".join(f"{r['rel']} {r['time']:.2f}s" for r in slow))
    print(f"total wall time: {wall:.1f}s over {len(results)} files")

    failed = sum(1 for r in results if not r["ok"])
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

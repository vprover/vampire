#!/opt/local/bin/python3.14
"""Are per-node instruction counts reproducible where wall times are not?

Runs each problem several times under a *deterministic* bound (--activation_limit,
with -t only as a watchdog) and reports, per node, the spread of instruction counts
against the spread of times across those runs.

The control comes first and matters as much as the measurement: before comparing any
node, the runs' statistics blocks are compared. If they differ, the *search* differed
between runs and a difference in per-node counts says nothing about the counters. The
usual cause is LRS, whose limits depend on elapsed time and instructions -- give -t
enough headroom that its estimate always exceeds the passive set, so it never
discards anything, and the search becomes deterministic.

    ./determinism.py                          # the default problem set
    ./determinism.py --runs 5 --al 40000
    ./determinism.py --problem PUZ016-1.p --problem HWV114-1.p

Expected: instruction spreads well under 0.1%, time spreads far larger. If instruction
spreads are also large *and* the statistics blocks match, the premise of counting
instructions is wrong and we should find out why before sweeping.
"""

import argparse
import os
import re
import statistics
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

# One per profile shape, chosen from the master-11131 sweep so that between them they
# exercise every TIME_TRACE node: AVATAR-heavy, superposition-heavy, arithmetic,
# polymorphic, higher-order, and one that is memory-heavy on purpose.
DEFAULT_PROBLEMS = [
    "HWV114-1.p",    # CNF,  SAT solver 70% of the run -- AVATAR and the SAT interface
    "PUZ016-1.p",    # CNF,  plain saturation, superposition + demodulation
    "SWW976_1.p",    # TX0,  the all-rounder: superposition, demodulation,
                     #       interpreted evaluation and unification with abstraction
    "SWV767_5.p",    # TF1,  polymorphic; exercises the type-argument paths
    "PUZ098^5.p",    # TH0,  the higher-order code path
    "BIO004+1.p",    # FOF,  881 MB in the sweep: the memory-bound case, where time
                     #       should move most and instructions should not
]

# lines whose value is *expected* to differ between runs
NOISE = re.compile(r"^% (Time elapsed|Instructions burned|Peak memory usage|Version|"
                   r"Termination reason)\b")


def run_once(binary, problem, al, timeout, extra):
    path = C.problem_path(problem)
    cmd = [binary, "-tstat", "on", "-p", "off",
           "-al", str(al), "-t", str(timeout)] + extra + [path]
    t0 = time.time()
    out = subprocess.run(cmd, capture_output=True, text=True,
                         cwd=C.ROOT).stdout
    return out, time.time() - t0


def stats_fingerprint(text):
    """The statistics block with the run-to-run-variable lines removed."""
    keep = []
    for ln in text.split("\n"):
        if ln.startswith("====="):
            break
        if ln.startswith("%") and not NOISE.match(ln):
            keep.append(ln.rstrip())
    return "\n".join(keep)


def spread(values):
    """max/min - 1, as a percentage; None if any value is missing or zero."""
    if not values or any(v is None for v in values):
        return None
    lo, hi = min(values), max(values)
    if lo <= 0:
        return None
    return 100.0 * (hi - lo) / lo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=None,
                    help="default: newest vampire_*_rel_* in the repo root")
    ap.add_argument("--problem", action="append", dest="problems")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--al", type=int, default=20000, help="--activation_limit")
    ap.add_argument("--timeout", type=int, default=600,
                    help="-t, a watchdog only; must be generous enough that LRS "
                         "never tightens its limits, or the search is not reproducible")
    ap.add_argument("--extra", default="", help="further options, space separated")
    ap.add_argument("--min-ms", type=float, default=1.0,
                    help="ignore nodes whose median time is below this many "
                         "milliseconds: their spread is clock granularity, not signal")
    a = ap.parse_args()

    binary = a.binary
    if not binary:
        cands = sorted((f for f in os.listdir(C.ROOT) if f.startswith("vampire_")
                        and "_rel_" in f),
                       key=lambda f: os.path.getmtime(os.path.join(C.ROOT, f)))
        if not cands:
            sys.exit("no vampire_*_rel_* binary found; pass --binary")
        binary = os.path.join(C.ROOT, cands[-1])
    extra = a.extra.split() if a.extra else []
    problems = a.problems or DEFAULT_PROBLEMS

    print(f"binary : {os.path.relpath(binary, C.ROOT)}")
    print(f"bound  : -al {a.al} -t {a.timeout} {' '.join(extra)}")
    print(f"runs   : {a.runs} per problem")
    print(f"nodes  : those whose median time is at least {a.min_ms} ms\n")

    table = C.Table("determinism",
                    [("problem", "problem", str),
                     ("search", "search", str),
                     ("bound", "bound", str),
                     ("nodes>=floor", "nodes", str),
                     ("instr spread med/max", "instr", str),
                     ("time spread med/max", "time", str)],
                    title="per-node spread across identical runs")

    for problem in problems:
        outs, walls = [], []
        for _ in range(a.runs):
            out, wall = run_once(binary, problem, a.al, a.timeout, extra)
            outs.append(out)
            walls.append(wall)

        reasons = {(re.search(r"^% Termination reason: (.*)$", o, re.M) or
                    [None, "?"])[1].strip() for o in outs}
        bound = "/".join(sorted(reasons))

        fps = {stats_fingerprint(o) for o in outs}
        search = "identical" if len(fps) == 1 else "DIFFERS"

        # per-node instruction and time series, from the flattened profile
        series_i, series_t = {}, {}
        ok = True
        for o in outs:
            root, rows = C.parse_flat(o)
            if root is None:
                ok = False
                break
            for name, t, _a, _c, instr in rows:
                series_i.setdefault(name, []).append(instr)
                series_t.setdefault(name, []).append(t)
        if not ok:
            table.add(dict(problem=problem, search=search, bound=bound,
                           nodes="unparsable", instr="-", time="-"))
            continue

        # A node that runs for a few nanoseconds has a meaningless spread (one clock
        # tick is 100% of it), and would otherwise dominate the max column.
        floor = a.min_ms * 1e6
        full = [n for n in series_i
                if len(series_i[n]) == a.runs
                and statistics.median(series_t[n]) >= floor]
        si = [s for n in full if (s := spread(series_i[n])) is not None]
        st = [s for n in full if (s := spread(series_t[n])) is not None]
        fmt = lambda v: (f"{statistics.median(v):.3f}% / {max(v):.3f}%"  # noqa: E731
                         if v else "-")
        table.add(dict(problem=problem, search=search, bound=bound,
                       nodes=str(len(full)), instr=fmt(si), time=fmt(st)))
        print(f"  {problem:16s} {search:9s} {bound:18s} "
              f"instr {fmt(si):22s} time {fmt(st)}", flush=True)

    print()
    table.emit(len(table.rows))
    print("\n  'search' compares the statistics blocks with the timing lines removed.\n"
          "  DIFFERS means the runs did not explore the same clauses, so their node\n"
          "  counts are not comparable -- raise -t until LRS stops tightening limits.\n"
          "  'bound' must read 'Activation limit': anything else means the run was cut\n"
          "  short somewhere non-deterministic.")


if __name__ == "__main__":
    main()

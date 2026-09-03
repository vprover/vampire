#!/opt/local/bin/python3.14
"""Cost per unit of work: runs where a node is much slower *per call* than usual.

This needs no peer model and no size model.  For each node we take the corpus
distribution of cost per call and ask, per run, how much would be given back if that
run's per-call cost were merely the corpus median:

    recoverable = cnt * (avg - median_avg)

Ranking by that puts "index degenerated on this problem" and "this data structure has a
bad case here" at the top, ordered by how much they are actually worth -- which is the
thing we want before touching any code.  A run that is simply *bigger* than the others
does not score, because `cnt` is divided out of `avg`.

Cost is counted in retired instructions by default.  That matters here more than in the
other reports: this one compares one run's per-call cost against another's, which is
exactly the comparison the sweep's machine noise corrupts, and which instruction counts
are immune to.

    ./rpt_percall.py                       # all nodes
    ./rpt_percall.py --metric time         # per-call nanoseconds instead
    ./rpt_percall.py --node "forward demodulation"
    ./rpt_percall.py --node-summary        # per-node spread: which nodes have bad cases
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

import numpy as np  # noqa: E402

MIN_CALLS = 1000            # below this, avg is clock noise
MIN_RECOVERABLE_NS = 10**9  # only report cases worth at least a second (or 1G instr)
OVERHEAD_NS = 26            # TIME_TRACE cost; nodes at this level measure themselves
# In the 11131 sweep `parsing` measured NFS latency rather than the parser and had to
# be excluded here. The 11142 sweep reads TPTP from local disk and the artifact is
# gone (SET044+1.p: 113 ms then, 212 us now), so nothing is excluded by default.
EXCLUDE = set()


def node_stats(con, key, metric):
    """Per-call cost of each node, per run, as (cost, problem, cnt, total)."""
    col = "self_instr" if metric == "instructions" else "self_ns"
    rows = con.execute(f"""
        SELECT {key} k, {col} c, cnt, problem FROM vtree
        WHERE cnt >= ? AND {col} IS NOT NULL
    """, (MIN_CALLS,)).fetchall()
    by = {}
    for r in rows:
        by.setdefault(r["k"], []).append((r["c"] / r["cnt"], r["problem"],
                                          r["cnt"], r["c"]))
    return by


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--node", action="append")
    ap.add_argument("--tree", action="store_true", help="group by path, not node name")
    ap.add_argument("--node-summary", action="store_true")
    ap.add_argument("--min-calls", type=int, default=MIN_CALLS)
    ap.add_argument("--limit", type=int, default=40)
    ap.add_argument("--include-parsing", action="store_true",
                    help="no longer needed: nothing is excluded by default now that "
                         "the sweep reads TPTP from local disk")
    ap.add_argument("--metric", choices=["instructions", "time"], default="instructions",
                    help="per-call cost measured in retired instructions (default) or "
                         "nanoseconds. Instructions are reproducible; time additionally "
                         "picks up cache behaviour and machine load")
    a = ap.parse_args()

    con = C.connect()
    key = "path" if a.tree else "node"
    by = node_stats(con, key, a.metric)
    # one formatter and one floor for whichever unit we are in
    fmt = C.fmt_n if a.metric == "instructions" else C.fmt_ns
    unit = "instr" if a.metric == "instructions" else "ns"
    # A node whose per-call cost is near the instrumentation cost measures itself.
    # In instructions that floor is unknown until calib_overhead is run with counters
    # on the sweep machine, so only apply it to time.
    floor = 0 if a.metric == "instructions" else OVERHEAD_NS * 3

    if a.node_summary:
        t = C.Table("percall_spread",
                    [("node", "k", str), ("runs", "n", C.fmt_n),
                     (f"median {unit}/call", "med", fmt), ("p90", "p90", fmt),
                     ("p99", "p99", fmt), ("max", "mx", fmt),
                     ("p99/median", "spread", lambda v: f"{v:.0f}x"),
                     ("total recoverable", "rec", fmt)],
                    title=f"per-call cost spread by node, in {a.metric} "
                          f"(runs with >= {a.min_calls} calls)")
        for k, vals in by.items():
            if len(vals) < 20 or (k in EXCLUDE and not a.include_parsing):
                continue
            arr = np.asarray([v[0] for v in vals])
            med = float(np.median(arr))
            rec = sum(c * (avg - med) for avg, _, c, _ in vals if avg > med)
            t.add(dict(k=k, n=len(vals), med=med,
                       p90=float(np.percentile(arr, 90)),
                       p99=float(np.percentile(arr, 99)), mx=float(arr.max()),
                       spread=float(np.percentile(arr, 99)) / max(med, 1e-9), rec=rec))
        t.rows.sort(key=lambda r: -r["rec"])
        t.emit(a.limit)
        print("\n  'total recoverable' = sum over runs of cnt*(avg-median) for the runs\n"
              "  above the median: the corpus-wide prize for removing this node's bad cases.")
        return

    t = C.Table("percall_outliers",
                [("problem", "problem", str), ("node", "k", str),
                 ("dialect", "dialect", str),
                 ("calls", "cnt", C.fmt_n),
                 (f"{unit}/call", "avg", fmt), ("median", "med", fmt),
                 ("x", "x", lambda v: f"{v:.0f}x"),
                 ("self", "self_ns", fmt),
                 ("recoverable", "rec", fmt),
                 ("szs", "szs", str)],
                title="runs where a node costs far more per call than it usually does")

    want = set(a.node) if a.node else None
    meta = {r["problem"]: r for r in con.execute(
        "SELECT problem, dialect, szs, termination FROM v").fetchall()}

    for k, vals in by.items():
        if want and k not in want:
            continue
        if not want and k in EXCLUDE and not a.include_parsing:
            continue
        if len(vals) < 20:
            continue
        med = float(np.median([v[0] for v in vals]))
        if med < floor:
            continue  # the node is too cheap for per-call cost to mean anything
        for avg, prob, cnt, self_ns in vals:
            rec = cnt * (avg - med)
            if rec < MIN_RECOVERABLE_NS or avg < 2 * med:
                continue
            m = meta.get(prob)
            t.add(dict(problem=prob, k=k, dialect=m["dialect"] if m else None,
                       cnt=cnt, avg=avg, med=med, x=avg / med, self_ns=self_ns,
                       rec=rec, szs=m["szs"] if m else None))
    t.rows.sort(key=lambda r: -r["rec"])
    t.emit(a.limit)
    print(f"\n  'recoverable' = cnt * (this run's {unit}/call - the corpus median).\n"
          "  Reproduce one with:  ./rerun.sh <problem>")
    con.close()


if __name__ == "__main__":
    main()

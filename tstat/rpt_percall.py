#!/opt/local/bin/python3.14
"""Cost per unit of work: runs where a node is much slower *per call* than usual.

This needs no peer model and no size model.  For each node we take the corpus
distribution of `self_ns / cnt` and ask, per run, how much time would be given back if
that run's per-call cost were merely the corpus median:

    recoverable = cnt * (avg - median_avg)

Ranking by that puts "index degenerated on this problem" and "this data structure has a
bad case here" at the top, ordered by how much they are actually worth -- which is the
thing we want before touching any code.  A run that is simply *bigger* than the others
does not score, because `cnt` is divided out of `avg`.

    ./rpt_percall.py                       # all nodes
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
MIN_RECOVERABLE_NS = 10**9  # only report cases worth at least a second
OVERHEAD_NS = 26            # TIME_TRACE cost; nodes at this level measure themselves
# `parsing` is excluded by default: in the reference sweep it is dominated by NFS
# latency on the server's TPTP mount, not by the parser (see README).
EXCLUDE = {"parsing", "parsing.term sharing", "parsing.sort sharing"}


def node_stats(con, key):
    """median and p90 of per-call cost, per node."""
    rows = con.execute(f"""
        SELECT {key} k, self_ns, cnt, problem FROM vtree WHERE cnt >= ?
    """, (MIN_CALLS,)).fetchall()
    by = {}
    for r in rows:
        by.setdefault(r["k"], []).append((r["self_ns"] / r["cnt"], r["problem"],
                                          r["cnt"], r["self_ns"]))
    return by


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--node", action="append")
    ap.add_argument("--tree", action="store_true", help="group by path, not node name")
    ap.add_argument("--node-summary", action="store_true")
    ap.add_argument("--min-calls", type=int, default=MIN_CALLS)
    ap.add_argument("--limit", type=int, default=40)
    ap.add_argument("--include-parsing", action="store_true")
    a = ap.parse_args()

    con = C.connect()
    key = "path" if a.tree else "node"
    by = node_stats(con, key)

    if a.node_summary:
        t = C.Table("percall_spread",
                    [("node", "k", str), ("runs", "n", C.fmt_n),
                     ("median/call", "med", C.fmt_ns), ("p90", "p90", C.fmt_ns),
                     ("p99", "p99", C.fmt_ns), ("max", "mx", C.fmt_ns),
                     ("p99/median", "spread", lambda v: f"{v:.0f}x"),
                     ("total recoverable", "rec", C.fmt_ns)],
                    title="per-call cost spread by node "
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
                 ("ns/call", "avg", C.fmt_ns), ("median", "med", C.fmt_ns),
                 ("x", "x", lambda v: f"{v:.0f}x"),
                 ("self", "self_ns", C.fmt_ns),
                 ("recoverable", "rec", C.fmt_ns),
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
        if med < OVERHEAD_NS * 3:
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
    print("\n  'recoverable' = cnt * (this run's ns/call - the corpus median ns/call).\n"
          "  Reproduce one with:  ./rerun.sh <problem>")
    con.close()


if __name__ == "__main__":
    main()

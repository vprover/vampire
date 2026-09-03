#!/opt/local/bin/python3.14
"""Instructions per second: how memory-bound was a run, and how noisy is the sweep?

`Instructions burned` is deterministic; `Time elapsed` is not.  Their ratio is the
run's effective IPC x clock.  It serves two purposes:

  --spread   how much the machine varied across the sweep.  With N jobs in parallel
             the runs contend for RAM and last-level cache, and this is the size of
             that effect.  If the spread is large, per-call wall-clock outliers are
             partly measuring the machine, not the code -- and the whole sweep would
             be better measured in instructions than in nanoseconds.

  (default)  runs with unusually low IPS.  Correlated with peak memory, these are the
             genuinely memory-bound ones: the index blew up and everything is a cache
             miss.  Per-node timings cannot tell that apart from "did more work".

    ./rpt_ips.py
    ./rpt_ips.py --spread
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

import numpy as np  # noqa: E402

MIN_INSTR_M = 5000   # 5G instructions: shorter runs are dominated by start-up


def rows(con):
    return con.execute("""
        SELECT problem, dialect, szs, termination, time_s, peak_mb, instr_M, family
        FROM v WHERE clean = 1 AND instr_M >= ? AND time_s > 0
    """, (MIN_INSTR_M,)).fetchall()


def spread(con):
    rs = rows(con)
    ips = np.asarray([r["instr_M"] / r["time_s"] for r in rs])  # M instr / s
    print(f"\ninstructions per second over {len(rs)} runs (>= {MIN_INSTR_M}M instructions)")
    print("-" * 72)
    qs = [1, 5, 10, 25, 50, 75, 90, 95, 99]
    v = np.percentile(ips, qs)
    for q, x in zip(qs, v):
        print(f"  p{q:<3d} {x:8.0f} M instr/s")
    med = float(np.median(ips))
    print(f"\n  p99/p1  = {v[-1]/v[0]:.1f}x   p90/p10 = {v[6]/v[2]:.2f}x")
    print(f"  a run at p10 takes {med/v[2]:.2f}x longer than the median run for the\n"
          f"  same work; at p1, {med/v[0]:.2f}x.  That factor is the floor on how much\n"
          "  any wall-clock comparison between two problems can be trusted.")

    print("\nby termination reason (instruction-limited runs all burn the same budget,\n"
          "so their time spread is purely machine/memory effects):")
    for term in sorted({r["termination"] for r in rs if r["termination"]}):
        s = np.asarray([r["instr_M"] / r["time_s"] for r in rs if r["termination"] == term])
        if len(s) < 30:
            continue
        print(f"  {term[:38]:38s} n={len(s):6d}  median {np.median(s):7.0f}  "
              f"p10/p90 {np.percentile(s,10):6.0f}/{np.percentile(s,90):6.0f} "
              f"({np.percentile(s,90)/np.percentile(s,10):.2f}x)")

    print("\nIPS vs peak memory (the memory-bound signature):")
    mem = np.asarray([r["peak_mb"] or 0 for r in rs], float)
    ok = mem > 0
    edges = [0, 64, 256, 1024, 4096, 16384, 10**9]
    for lo, hi in zip(edges, edges[1:]):
        m = ok & (mem >= lo) & (mem < hi)
        if m.sum() < 30:
            continue
        print(f"  {lo:6d}-{hi if hi < 10**8 else 0:6d} MB  n={m.sum():6d}  "
              f"median {np.median(ips[m]):7.0f} M instr/s")


def outliers(con, limit):
    rs = rows(con)
    ips = {r["problem"]: r["instr_M"] / r["time_s"] for r in rs}
    med = float(np.median(list(ips.values())))
    t = C.Table("ips_outliers",
                [("problem", "problem", str), ("dialect", "dialect", str),
                 ("M instr/s", "ips", lambda v: f"{v:,.0f}"),
                 ("x slower", "x", lambda v: f"{v:.1f}x"),
                 ("time", "time_s", lambda v: f"{v:.0f}s"),
                 ("instr", "instr_M", lambda v: f"{v/1000:.0f}G"),
                 ("peak mem", "peak_mb", lambda v: f"{v}MB"),
                 ("lost", "lost_s", lambda v: f"{v:.0f}s"),
                 ("szs", "szs", str)],
                title="memory-bound runs: far fewer instructions per second than usual")
    for r in rs:
        x = med / ips[r["problem"]]
        if x < 1.6:
            continue
        lost = r["time_s"] - r["instr_M"] / med
        if lost < 10:
            continue
        t.add(dict(problem=r["problem"], dialect=r["dialect"], ips=ips[r["problem"]],
                   x=x, time_s=r["time_s"], instr_M=r["instr_M"],
                   peak_mb=r["peak_mb"], lost_s=lost, szs=r["szs"]))
    t.rows.sort(key=lambda r: -r["lost_s"])
    t.emit(limit)
    print(f"\n  median across the sweep is {med:,.0f} M instr/s; 'lost' is the wall time\n"
          "  this run spent above what its instruction count would take at that rate.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--spread", action="store_true")
    ap.add_argument("--limit", type=int, default=35)
    a = ap.parse_args()
    con = C.connect()
    if a.spread:
        spread(con)
    else:
        outliers(con, a.limit)
    con.close()


if __name__ == "__main__":
    main()

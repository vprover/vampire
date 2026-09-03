#!/opt/local/bin/python3.14
"""Where the default strategy actually burns time.

Two aggregations, because they answer different questions:

  sum      total exclusive (self) time summed over the corpus, as % of all measured
           time.  Dominated by the instruction-limited runs, which all burn the same
           budget -- so this is "where does a compute-bound run spend its cycles".
  mean     the mean over runs of each node's per-run share.  Every problem counts
           once, so a node that is huge on a handful of runs cannot dominate.

A node is only worth optimising if it is high in *both*, or if the gap between them
is itself the story (concentrated vs. pervasive cost).

    ./rpt_hotspots.py                 # corpus-wide
    ./rpt_hotspots.py --by-dialect    # one table per TPTP dialect
    ./rpt_hotspots.py --tree          # path-qualified, so `term sharing` under
                                      # parsing is separated from the one in the loop
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

# `steady_clock::now()` costs ~20-25ns and TIME_TRACE takes two of them, so a node
# whose average is near this is measuring mostly itself.  See calib_overhead.py.
DEFAULT_OVERHEAD_NS = 26   # measured by calib_overhead.py on this machine


def hotspots(con, where, params, overhead, key, title, limit):
    keyexpr = "path" if key == "path" else "node"
    rows = con.execute(f"""
        WITH runtot AS (
          SELECT problem, SUM(self_ns) tot FROM vtree WHERE {where} GROUP BY problem
        )
        SELECT t.{keyexpr} k,
               SUM(t.self_ns)        sum_ns,
               SUM(t.cnt)            calls,
               COUNT(DISTINCT t.problem) runs,
               AVG(1.0 * t.self_ns / MAX(runtot.tot, 1)) mean_share
        FROM vtree t JOIN runtot USING(problem)
        WHERE {where}
        GROUP BY 1
    """, params + params).fetchall()

    corpus = con.execute(f"""
        SELECT SUM(self_ns) s, COUNT(DISTINCT problem) n FROM vtree WHERE {where}
    """, params).fetchone()
    total, nruns = corpus["s"] or 1, corpus["n"] or 1

    t = C.Table(
        "hotspots_" + title.replace(" ", "_").replace("/", "_"),
        [("node" if key == "node" else "path", "k", str),
         ("self", "sum_ns", C.fmt_ns),
         ("%corpus", "pct", lambda x: f"{x:.2f}%"),
         ("mean%/run*", "mean_pct", lambda x: f"{x:.2f}%"),
         ("calls", "calls", C.fmt_n),
         ("avg", "avg_ns", C.fmt_ns),
         ("instr%", "instr_pct", lambda x: f"{x:.0f}%"),
         ("runs", "runs", C.fmt_n)],
        title=f"{title}  ({nruns} runs, {total/1e9:,.0f}s of exclusive time)")

    for r in sorted(rows, key=lambda r: -(r["sum_ns"] or 0)):
        calls = r["calls"] or 0
        avg = (r["sum_ns"] or 0) / max(calls, 1)
        t.add(dict(k=r["k"], sum_ns=r["sum_ns"], pct=100 * (r["sum_ns"] or 0) / total,
                   mean_pct=100 * (r["mean_share"] or 0), calls=calls, avg_ns=avg,
                   # what fraction of this node's measured time is the profiler itself
                   instr_pct=min(100.0, 100.0 * overhead * calls / max(r["sum_ns"], 1)),
                   runs=r["runs"]))
    t.emit(limit)
    print("\n  mean%/run* = mean of the node's per-run share, over the `runs` runs where it\n"
          "               occurs at all -- i.e. conditional on the node being exercised.\n"
          "  instr%     = share of this node's time that is TIME_TRACE overhead itself\n"
          f"               (at {overhead}ns per scoped timer); >30% means the number is\n"
          "               mostly instrumentation, not work.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--by-dialect", action="store_true")
    ap.add_argument("--tree", action="store_true", help="group by tree path, not node name")
    ap.add_argument("--overhead", type=int, default=DEFAULT_OVERHEAD_NS)
    ap.add_argument("--termination", default=None,
                    help="restrict to one termination reason, e.g. 'Refutation'")
    ap.add_argument("--limit", type=int, default=45)
    a = ap.parse_args()

    con = C.connect()
    key = "path" if a.tree else "node"
    where, params = "1=1", []
    if a.termination:
        where, params = "termination = ?", [a.termination]

    if a.by_dialect:
        for d in [r["dialect"] for r in
                  con.execute("SELECT dialect, COUNT(*) c FROM v WHERE clean=1 "
                              "GROUP BY 1 ORDER BY c DESC").fetchall() if r["dialect"]]:
            hotspots(con, where + " AND dialect = ?", params + [d], a.overhead, key,
                     f"dialect {d}", a.limit)
    else:
        hotspots(con, where, params, a.overhead, key, "corpus", a.limit)
    con.close()


if __name__ == "__main__":
    main()

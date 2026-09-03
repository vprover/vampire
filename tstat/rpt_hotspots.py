#!/opt/local/bin/python3.14
"""Where the default strategy actually burns its work.

Two aggregations, because they answer different questions:

  sum      total exclusive (self) cost summed over the corpus, as % of all measured
           cost.  Dominated by the instruction-limited runs, which all burn the same
           budget -- so this is "where does a compute-bound run spend its cycles".
  mean     the mean over runs of each node's per-run share.  Every problem counts
           once, so a node that is huge on a handful of runs cannot dominate.

A node is only worth optimising if it is high in *both*, or if the gap between them
is itself the story (concentrated vs. pervasive cost).

Ranking is by *instructions* by default. Time and instructions genuinely disagree --
`LRS limit maintenance` is 19.4% of corpus time but 6.6% of instructions -- so the
choice matters. Instructions measure work done and are reproducible; time additionally
reflects cache behaviour, which the `t/i` and `ps/instr` columns isolate.

    ./rpt_hotspots.py                     # corpus-wide, by instructions
    ./rpt_hotspots.py --metric time       # the old ranking, for comparison
    ./rpt_hotspots.py --metric membound   # by ps/instr: which nodes stall on memory
    ./rpt_hotspots.py --by-dialect        # one table per TPTP dialect
    ./rpt_hotspots.py --tree              # path-qualified, so `term sharing` under
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

# --metric membound ignores nodes below this share of corpus instructions: ps/instr
# is a ratio, and a node with few calls can post an arbitrary one.
MEMBOUND_FLOOR = 0.001


def hotspots(con, where, params, overhead, key, title, limit, metric="instructions"):
    """`metric` selects the column that ranks the table and drives the % shares.

    Time and instructions disagree substantially -- on the 11142 sweep
    `LRS limit maintenance` is 19.9% of time but 6.7% of instructions -- so which
    one ranks the table is a real choice, not cosmetic. Instructions are the
    default because they are the reproducible measure of work done; the ps/instr
    column carries the memory-bound story that only time can tell.
    """
    keyexpr = "path" if key == "path" else "node"
    # rank on `self_instr` or `self_ns`; both are always fetched, since the report
    # shows the ratio between them regardless of which one sorts.
    m = "self_ns" if metric == "time" else "self_instr"
    rows = con.execute(f"""
        WITH runtot AS (
          SELECT problem, SUM({m}) tot FROM vtree WHERE {where} GROUP BY problem
        )
        SELECT t.{keyexpr} k,
               SUM(t.self_ns)        sum_ns,
               SUM(t.self_instr)     sum_instr,
               SUM(t.cnt)            calls,
               COUNT(DISTINCT t.problem) runs,
               AVG(1.0 * t.{m} / MAX(runtot.tot, 1)) mean_share
        FROM vtree t JOIN runtot USING(problem)
        WHERE {where}
        GROUP BY 1
    """, params + params).fetchall()

    corpus = con.execute(f"""
        SELECT SUM(self_ns) s, SUM(self_instr) i, COUNT(DISTINCT problem) n
        FROM vtree WHERE {where}
    """, params).fetchone()
    tot_ns, tot_instr = corpus["s"] or 1, corpus["i"] or 1
    nruns = corpus["n"] or 1
    total = tot_instr if metric == "instructions" else tot_ns

    # corpus-average picoseconds per instruction, the baseline a node's own rate is
    # only interesting relative to
    base_ps = 1000.0 * tot_ns / tot_instr

    t = C.Table(
        "hotspots_" + title.replace(" ", "_").replace("/", "_"),
        [("node" if key == "node" else "path", "k", str),
         ("self instr", "sum_instr", C.fmt_n),
         ("%instr", "pct_i", lambda x: f"{x:.2f}%"),
         ("self time", "sum_ns", C.fmt_ns),
         ("%time", "pct_t", lambda x: f"{x:.2f}%"),
         ("t/i", "skew", lambda x: f"{x:.2f}x"),
         ("ps/instr", "ps", lambda x: f"{x:.0f}" if x else "-"),
         ("mean%/run*", "mean_pct", lambda x: f"{x:.2f}%"),
         ("calls", "calls", C.fmt_n),
         ("avg", "avg_ns", C.fmt_ns),
         ("ovh%", "ovh_pct", lambda x: f"{x:.0f}%"),
         ("runs", "runs", C.fmt_n)],
        title=f"{title}  ({nruns} runs, {tot_ns/1e9:,.0f}s / {tot_instr/1e12:,.0f}T instr "
              f"exclusive, ranked by {metric})")

    if metric == "membound":
        # Rank by ps/instr, but only among nodes big enough for the ratio to mean
        # anything -- a node with a handful of calls can post any rate at all.
        floor = MEMBOUND_FLOOR * tot_instr
        rows = [r for r in rows if (r["sum_instr"] or 0) >= floor]
        ranked = sorted(rows, key=lambda r: -(1000.0 * (r["sum_ns"] or 0) /
                                              max(r["sum_instr"] or 1, 1)))
    else:
        rank = "sum_instr" if metric == "instructions" else "sum_ns"
        ranked = sorted(rows, key=lambda r: -(r[rank] or 0))
    for r in ranked:
        calls = r["calls"] or 0
        ns, instr = r["sum_ns"] or 0, r["sum_instr"] or 0
        pct_t, pct_i = 100 * ns / tot_ns, 100 * instr / tot_instr
        t.add(dict(k=r["k"], sum_ns=ns, sum_instr=instr,
                   pct_t=pct_t, pct_i=pct_i,
                   # >1 means wall clock over-ranks this node relative to work done
                   skew=(pct_t / pct_i) if pct_i else None,
                   ps=(1000.0 * ns / instr) if instr else None,
                   mean_pct=100 * (r["mean_share"] or 0), calls=calls,
                   avg_ns=ns / max(calls, 1),
                   # what fraction of this node's measured time is the profiler itself
                   ovh_pct=min(100.0, 100.0 * overhead * calls / max(ns, 1)),
                   runs=r["runs"]))
    t.emit(limit)
    print(f"\n  %instr/%time = share of corpus exclusive instructions / time.\n"
          f"  t/i        = %time divided by %instr. Above 1 the node is memory-bound:\n"
          f"               wall clock over-ranks it relative to the work it does.\n"
          f"  ps/instr   = picoseconds per instruction; corpus average is {base_ps:.0f}.\n"
          "  mean%/run* = mean of the node's per-run share, over the `runs` runs where it\n"
          "               occurs at all -- i.e. conditional on the node being exercised.\n"
          "  ovh%       = share of this node's *time* that is TIME_TRACE overhead itself\n"
          f"               (at {overhead}ns per scoped timer); >30% means the number is\n"
          "               mostly instrumentation, not work.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--by-dialect", action="store_true")
    ap.add_argument("--tree", action="store_true", help="group by tree path, not node name")
    ap.add_argument("--overhead", type=int, default=DEFAULT_OVERHEAD_NS)
    ap.add_argument("--metric", choices=["instructions", "time", "membound"], default="instructions",
                    help="which measure ranks the table and sets the %% shares. "
                         "Instructions by default: they are reproducible where time is "
                         "not, and time over-ranks memory-bound nodes (see the t/i column)")
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
                     f"dialect {d}", a.limit, a.metric)
    else:
        hotspots(con, where, params, a.overhead, key, "corpus", a.limit, a.metric)
    con.close()


if __name__ == "__main__":
    main()

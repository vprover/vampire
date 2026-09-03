#!/opt/local/bin/python3.14
"""Saturation runs whose time breakdown differs from their peers.

There is no upper bound on how long saturation may run, so absolute time says little.
What is informative is a run spending its time *differently* from problems that are
otherwise the same.  Peer groups, in order of preference:

  family   the TPTP problem number without its variant suffix -- CSR115+1..+15,
           SWV422-1.001..016, PLA031-1.004..  These are near-identical problems, so a
           profile difference inside a family is almost always about the prover, not
           about the problem.
  bucket   fallback for problems with no siblings: dialect x size decile x SZS status.

For each (run, node) we compare the node's share of the run's main-loop time against
the peer median, scored with a MAD-robust z.  Only deviations that are also worth real
time are reported.

    ./rpt_peers.py                 # families, then buckets
    ./rpt_peers.py --group family
    ./rpt_peers.py --family CSR115 # print the whole family's profile side by side
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

import numpy as np  # noqa: E402

MIN_GROUP = 4              # a peer group needs this many runs to have a median
MIN_LOOP_NS = 2 * 10**9    # ignore runs that barely entered saturation
MIN_DEVIATION_NS = 2 * 10**9
MIN_Z = 4.0


def load_profiles(con):
    """{problem: {node: self_ns}} plus per-run main-loop totals, saturation nodes only."""
    rows = con.execute("""
        SELECT problem, node, SUM(self_ns) s FROM vtree
        WHERE path LIKE 'main loop%' GROUP BY 1, 2
    """).fetchall()
    prof, loop = {}, {}
    for r in rows:
        prof.setdefault(r["problem"], {})[r["node"]] = r["s"]
        loop[r["problem"]] = loop.get(r["problem"], 0) + r["s"]
    return prof, {p: v for p, v in loop.items() if v >= MIN_LOOP_NS}


def groups_by_family(con, loop):
    g = {}
    for r in con.execute("SELECT problem, family FROM v WHERE clean=1"):
        if r["problem"] in loop:
            g.setdefault(r["family"], []).append(r["problem"])
    return {k: v for k, v in g.items() if len(v) >= MIN_GROUP}


def groups_by_bucket(con, loop):
    rows = [r for r in con.execute(
        "SELECT problem, dialect, size, szs FROM v WHERE clean=1").fetchall()
        if r["problem"] in loop and r["size"]]
    sizes = np.asarray([r["size"] for r in rows], float)
    edges = np.percentile(sizes, np.arange(10, 100, 10)) if len(sizes) > 10 else []
    g = {}
    for r in rows:
        dec = int(np.searchsorted(edges, r["size"]))
        g.setdefault((r["dialect"], dec, r["szs"]), []).append(r["problem"])
    return {k: v for k, v in g.items() if len(v) >= MIN_GROUP}


def score(prof, loop, groups, label, t, meta):
    for gid, members in groups.items():
        nodes = set()
        for p in members:
            nodes |= set(prof.get(p, {}))
        for node in nodes:
            shares = np.asarray([prof.get(p, {}).get(node, 0) / loop[p] for p in members])
            med = float(np.median(shares))
            mad = 1.4826 * float(np.median(np.abs(shares - med)))
            if mad <= 0:
                continue
            for p, sh in zip(members, shares):
                z = (sh - med) / mad
                excess = (sh - med) * loop[p]
                if z < MIN_Z or excess < MIN_DEVIATION_NS:
                    continue
                m = meta.get(p, {})
                t.add(dict(problem=p, group=f"{label}:{gid}", peers=len(members),
                           node=node, share=100 * sh, peer_share=100 * med, z=float(z),
                           excess=excess, loop=loop[p],
                           szs=m.get("szs"), dialect=m.get("dialect"),
                           siblings=" ".join(sorted(q for q in members if q != p)[:4])))


def show_family(con, prof, loop, fam):
    members = sorted(r["problem"] for r in con.execute(
        "SELECT problem FROM v WHERE family=? AND clean=1", (fam,)) if r["problem"] in loop)
    if not members:
        print(f"no usable runs in family {fam}")
        return
    nodes = sorted({n for p in members for n in prof.get(p, {})},
                   key=lambda n: -sum(prof.get(p, {}).get(n, 0) for p in members))[:14]
    w = max(len(p) for p in members) + 2
    print(f"\nfamily {fam}: share of main-loop time per node (%)\n")
    print("problem".ljust(w) + "loop".rjust(8) +
          "".join(n[:11].rjust(13) for n in nodes))
    print("-" * (w + 8 + 13 * len(nodes)))
    for p in members:
        row = "".join(f"{100*prof.get(p,{}).get(n,0)/loop[p]:12.1f} " for n in nodes)
        print(p.ljust(w) + C.fmt_ns(loop[p]).rjust(8) + row)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", choices=["family", "bucket", "both"], default="both")
    ap.add_argument("--family", help="dump one family's full profile table")
    ap.add_argument("--limit", type=int, default=35)
    a = ap.parse_args()

    con = C.connect()
    prof, loop = load_profiles(con)
    if a.family:
        show_family(con, prof, loop, a.family)
        return
    meta = {r["problem"]: dict(r) for r in
            con.execute("SELECT problem, dialect, szs FROM v")}

    t = C.Table("peer_outliers",
                [("problem", "problem", str), ("dialect", "dialect", str),
                 ("node", "node", str),
                 ("share", "share", lambda v: f"{v:.1f}%"),
                 ("peers", "peer_share", lambda v: f"{v:.1f}%"),
                 ("z", "z", lambda v: f"{v:.0f}"),
                 ("excess", "excess", C.fmt_ns),
                 ("group", "group", str), ("n", "peers", str),
                 ("compare with", "siblings", str)],
                title="runs spending their saturation time unlike their peers")

    if a.group in ("family", "both"):
        score(prof, loop, groups_by_family(con, loop), "fam", t, meta)
    if a.group in ("bucket", "both"):
        score(prof, loop, groups_by_bucket(con, loop), "bkt", t, meta)
    t.rows.sort(key=lambda r: -r["excess"])
    t.emit(a.limit)
    print("\n  'share' is the node's fraction of this run's main-loop time, 'peers' the\n"
          "  group median; 'excess' is what that difference costs in wall time.\n"
          "  Inspect a whole family with:  ./rpt_peers.py --family CSR115")
    con.close()


if __name__ == "__main__":
    main()

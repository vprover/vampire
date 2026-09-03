#!/opt/local/bin/python3.14
"""Preprocessing cost vs. input size: is any step superlinear, and which problems
cost far more than their size predicts?

Everything before saturation should be roughly linear in the size of the input.  Two
views:

  --fit       per (dialect, node), a Theil-Sen fit of log(self_ns) ~ a + b*log(size)
              with a bootstrap CI on the exponent b.  b ~ 1 is linear, b ~ 2 is
              quadratic and *is* the finding.  Size is the TPTP header's
              atoms+connectives+variables, which is an input measure computed by
              TPTP itself, so it cannot be biased by anything Vampire does.

  --outliers  problems whose preprocessing cost sits far above that fit
              (studentised residual), with the sub-node breakdown showing which step
              is responsible and the peer problems to compare against.

  --percost   the model-free view: ns per input atom, descending, floored at a
              minimum size so noise cannot win.

    ./rpt_preproc.py                    # all three
    ./rpt_preproc.py --node parsing     # restrict to one step
"""

import argparse
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

import numpy as np  # noqa: E402

# The pre-saturation steps.  Path-qualified where a name also occurs inside the main
# loop, so we never mix parse-time term sharing with the saturation-time one.
PREPROC_PATHS = [
    "parsing",
    "parsing.term sharing",
    "parsing.sort sharing",
    "preprocessing",
    "preprocessing.property evaluation",
    "preprocessing.naming",
    "preprocessing.sine selection",
    "preprocessing.term sharing",
    "preprocessing.shuffling things",
    "property evaluation",
]
MIN_SIZE = 200          # below this the TPTP header metrics are too coarse to fit
MIN_NS = 1_000_000      # 1ms: below this the measurement is mostly clock noise


def load(con, path, dialect=None):
    """(size, self_ns, problem) triples for one tree path."""
    q = """SELECT problem, size, self_ns FROM vtree
           WHERE path = ? AND size >= ? AND self_ns >= ?"""
    p = [path, MIN_SIZE, MIN_NS]
    if dialect:
        q += " AND dialect = ?"
        p.append(dialect)
    rows = con.execute(q, p).fetchall()
    return ([r["size"] for r in rows], [r["self_ns"] for r in rows],
            [r["problem"] for r in rows])


def theil_sen(x, y, max_pairs=200_000, rng=None):
    """Median pairwise slope -- robust to the heavy tail we expect here."""
    n = len(x)
    if n < 8:
        return None, None
    rng = rng or random.Random(0)
    idx = range(n)
    pairs = n * (n - 1) // 2
    slopes = []
    if pairs <= max_pairs:
        for i in range(n):
            for j in range(i + 1, n):
                if x[j] != x[i]:
                    slopes.append((y[j] - y[i]) / (x[j] - x[i]))
    else:
        for _ in range(max_pairs):
            i, j = rng.randrange(n), rng.randrange(n)
            if i != j and x[i] != x[j]:
                slopes.append((y[j] - y[i]) / (x[j] - x[i]))
    if not slopes:
        return None, None
    slopes = np.asarray(slopes)
    b = float(np.median(slopes))
    a = float(np.median(np.asarray(y) - b * np.asarray(x)))
    return a, b


def fit_report(con, nodes, dialects, limit):
    t = C.Table("preproc_fit",
                [("dialect", "dialect", str), ("step", "path", str),
                 ("n", "n", C.fmt_n),
                 ("exponent b", "b", lambda v: f"{v:.2f}"),
                 ("95% CI", "ci", str),
                 ("verdict", "verdict", str),
                 ("median ns/atom", "per", lambda v: f"{v:.0f}")],
                title="complexity fit:  log(self time) ~ a + b*log(input size)")
    rng = random.Random(1)
    for d in dialects:
        for path in nodes:
            xs, ys, _ = load(con, path, d)
            if len(xs) < 30:
                continue
            lx = [math.log(v) for v in xs]
            ly = [math.log(v) for v in ys]
            a, b = theil_sen(lx, ly, rng=rng)
            if b is None:
                continue
            # bootstrap the exponent
            bs = []
            n = len(lx)
            for _ in range(60):
                s = [rng.randrange(n) for _ in range(min(n, 400))]
                _, bb = theil_sen([lx[i] for i in s], [ly[i] for i in s], rng=rng)
                if bb is not None:
                    bs.append(bb)
            lo, hi = (np.percentile(bs, [2.5, 97.5]) if bs else (float("nan"),) * 2)
            verdict = ("LINEAR" if hi < 1.25 else
                       "superlinear" if lo > 1.25 and hi < 1.75 else
                       "QUADRATIC?" if lo >= 1.75 else "unclear")
            per = float(np.median([y / x for x, y in zip(xs, ys)]))
            t.add(dict(dialect=d, path=path, n=len(xs), b=b,
                       ci=f"[{lo:.2f}, {hi:.2f}]", verdict=verdict, per=per))
    t.rows.sort(key=lambda r: -r["b"])
    t.emit(limit)
    print("\n  b is the fitted exponent: 1.0 = linear in input size, 2.0 = quadratic.\n"
          "  Only rows with n >= 30 and self time >= 1ms are fitted.")


def outlier_report(con, nodes, dialects, limit):
    t = C.Table("preproc_outliers",
                [("problem", "problem", str), ("dialect", "dialect", str),
                 ("step", "path", str), ("size", "size", C.fmt_n),
                 ("self", "self_ns", C.fmt_ns),
                 ("predicted", "pred_ns", C.fmt_ns),
                 ("x over", "ratio", lambda v: f"{v:.0f}x"),
                 ("resid z", "z", lambda v: f"{v:.1f}"),
                 ("szs", "szs", str)],
                title="problems whose pre-saturation cost far exceeds their size")
    rng = random.Random(2)
    for d in dialects:
        for path in nodes:
            xs, ys, probs = load(con, path, d)
            if len(xs) < 30:
                continue
            lx = np.log(np.asarray(xs, float))
            ly = np.log(np.asarray(ys, float))
            a, b = theil_sen(list(lx), list(ly), rng=rng)
            if b is None:
                continue
            resid = ly - (a + b * lx)
            # robust scale: MAD, so the outliers do not inflate their own yardstick
            scale = 1.4826 * float(np.median(np.abs(resid - np.median(resid)))) or 1e-9
            z = (resid - np.median(resid)) / scale
            for i in np.argsort(-z)[:60]:
                if z[i] < 6:
                    break
                r = con.execute("SELECT szs FROM v WHERE problem=?", (probs[i],)).fetchone()
                t.add(dict(problem=probs[i], dialect=d, path=path, size=xs[i],
                           self_ns=ys[i], pred_ns=math.exp(a + b * lx[i]),
                           ratio=ys[i] / math.exp(a + b * lx[i]), z=float(z[i]),
                           szs=r["szs"] if r else None))
    t.rows.sort(key=lambda r: -r["z"])
    t.emit(limit)
    print("\n  'predicted' is what the per-dialect fit expects for a problem this size;\n"
          "  'resid z' is a MAD-robust z-score of log(actual/predicted).")


def percost_report(con, nodes, limit):
    t = C.Table("preproc_percost",
                [("problem", "problem", str), ("dialect", "dialect", str),
                 ("step", "path", str), ("size", "size", C.fmt_n),
                 ("self", "self_ns", C.fmt_ns),
                 ("ns/atom", "per", lambda v: f"{v:,.0f}"),
                 ("x median", "x", lambda v: f"{v:.0f}x"), ("szs", "szs", str)],
                title="model-free: nanoseconds of pre-saturation time per input atom")
    for path in nodes:
        rows = con.execute("""
            SELECT problem, dialect, size, self_ns, szs FROM vtree
            WHERE path = ? AND size >= ? AND self_ns >= ?
        """, (path, MIN_SIZE, MIN_NS)).fetchall()
        if len(rows) < 30:
            continue
        per = {r["problem"]: r["self_ns"] / r["size"] for r in rows}
        med = float(np.median(list(per.values())))
        for r in sorted(rows, key=lambda r: -per[r["problem"]])[:40]:
            t.add(dict(problem=r["problem"], dialect=r["dialect"], path=path,
                       size=r["size"], self_ns=r["self_ns"], per=per[r["problem"]],
                       x=per[r["problem"]] / med, szs=r["szs"]))
    t.rows.sort(key=lambda r: -r["x"])
    t.emit(limit)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--node", action="append", help="restrict to these tree paths")
    ap.add_argument("--dialect", action="append")
    ap.add_argument("--fit", action="store_true")
    ap.add_argument("--outliers", action="store_true")
    ap.add_argument("--percost", action="store_true")
    ap.add_argument("--limit", type=int, default=35)
    a = ap.parse_args()
    if not (a.fit or a.outliers or a.percost):
        a.fit = a.outliers = a.percost = True

    con = C.connect()
    nodes = a.node or PREPROC_PATHS
    dialects = a.dialect or [r["dialect"] for r in con.execute(
        "SELECT dialect, COUNT(*) c FROM v WHERE clean=1 AND dialect IS NOT NULL "
        "GROUP BY 1 ORDER BY c DESC").fetchall()]
    if a.fit:
        fit_report(con, nodes, dialects, a.limit)
    if a.outliers:
        outlier_report(con, nodes, dialects, a.limit)
    if a.percost:
        percost_report(con, nodes, a.limit)
    con.close()


if __name__ == "__main__":
    main()

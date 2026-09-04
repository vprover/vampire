#!/opt/local/bin/python3.14
"""Ingest a `-tstat on` sweep into tstat/tstat.db.

    ./ingest.py                 # full ingest (~1-2 min over 26.5k logs)
    ./ingest.py --selftest      # integrity checks against the built DB
    ./ingest.py --logdir DIR    # ingest a different sweep

Schema
------
runs        one row per log, including rejected ones (clean=0) so we can check that
            filtering does not silently drop a whole dialect
tptp        TPTP header metrics per problem (input size, independent of Vampire)
stats       long form of the `% Label | proof | total` statistics block
nodes_flat  the flattened time profile: one row per (problem, node)
nodes_tree  the nesting trace tree: one row per (problem, path), with self_ns
meta        key/value scalars (sweep dir, timer overhead calibration, ...)
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

DDL = """
DROP TABLE IF EXISTS runs;
DROP TABLE IF EXISTS tptp;
DROP TABLE IF EXISTS stats;
DROP TABLE IF EXISTS nodes_flat;
DROP TABLE IF EXISTS nodes_tree;
DROP TABLE IF EXISTS meta;

CREATE TABLE runs (
  problem      TEXT PRIMARY KEY,
  domain       TEXT,
  family       TEXT,
  szs          TEXT,
  termination  TEXT,
  time_s       REAL,
  peak_mb      INTEGER,
  instr_M      INTEGER,
  signal       TEXT,
  user_error   TEXT,
  root_ns      INTEGER,   -- from the flattened profile
  root_instr   INTEGER,   -- ditto, the whole run's retired instructions
  tree_root_ns INTEGER,   -- from the trace tree (should agree)
  clean        INTEGER,   -- 1 = flattened profile trustworthy
  tree_clean   INTEGER,   -- 1 = trace tree trustworthy
  reject       TEXT,
  tree_reject  TEXT,
  log_bytes    INTEGER
);

CREATE TABLE tptp (
  problem  TEXT PRIMARY KEY,
  spc      TEXT,
  dialect  TEXT,
  tptp_status TEXT,
  rating   REAL,
  formulae INTEGER, atoms INTEGER, equ_atoms INTEGER, max_formula_atoms INTEGER,
  connectives INTEGER, max_formula_depth INTEGER, max_term_depth INTEGER,
  predicates INTEGER, functors INTEGER, symbols INTEGER, variables INTEGER,
  types INTEGER, type_conns INTEGER,
  size INTEGER            -- atoms + connectives + variables: the input-size measure
);

CREATE TABLE stats (
  problem TEXT, section TEXT, label TEXT, proof INTEGER, total INTEGER
);

CREATE TABLE nodes_flat (
  problem TEXT, node TEXT, total_ns INTEGER, avg_ns INTEGER, cnt INTEGER,
  instr INTEGER          -- NULL when the run had no hardware instruction counter
);

CREATE TABLE nodes_tree (
  problem TEXT, path TEXT, node TEXT, depth INTEGER,
  total_ns INTEGER, avg_ns INTEGER, cnt INTEGER, instr INTEGER,
  self_ns INTEGER, self_instr INTEGER
);

CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
"""

INDEXES = """
CREATE INDEX ix_flat_node ON nodes_flat(node);
CREATE INDEX ix_flat_prob ON nodes_flat(problem);
CREATE INDEX ix_tree_node ON nodes_tree(node);
CREATE INDEX ix_tree_path ON nodes_tree(path);
CREATE INDEX ix_tree_prob ON nodes_tree(problem);
CREATE INDEX ix_stats_label ON stats(label);
CREATE INDEX ix_stats_prob ON stats(problem);
CREATE INDEX ix_runs_clean ON runs(clean);
CREATE INDEX ix_tptp_dialect ON tptp(dialect);
"""

# Convenience view: everything a report normally needs, already joined and filtered.
VIEWS = """
DROP VIEW IF EXISTS v;
CREATE VIEW v AS
SELECT r.problem, r.domain, r.family, t.dialect, t.spc, t.tptp_status, t.rating,
       t.size, t.atoms, t.formulae, t.max_term_depth,
       r.szs, r.termination, r.time_s, r.peak_mb, r.instr_M,
       r.root_ns, r.root_instr, r.clean, r.tree_clean, r.user_error, r.signal
FROM runs r LEFT JOIN tptp t USING(problem);

DROP VIEW IF EXISTS vflat;
CREATE VIEW vflat AS
SELECT f.problem, f.node, f.total_ns, f.avg_ns, f.cnt, f.instr,
       v.dialect, v.family, v.size, v.szs, v.termination, v.root_ns, v.root_instr,
       v.time_s
FROM nodes_flat f JOIN v USING(problem)
WHERE v.clean = 1;

DROP VIEW IF EXISTS vtree;
CREATE VIEW vtree AS
SELECT n.problem, n.path, n.node, n.depth, n.total_ns, n.avg_ns, n.cnt,
       n.instr, n.self_ns, n.self_instr,
       -- picoseconds per instruction: the per-node memory-boundedness signal
       CASE WHEN n.self_instr > 0 THEN 1000.0 * n.self_ns / n.self_instr END ps_per_instr,
       v.dialect, v.family, v.size, v.szs, v.termination, v.root_ns, v.root_instr,
       v.time_s
FROM nodes_tree n JOIN v USING(problem)
WHERE v.tree_clean = 1;
"""


def ingest(logdir, db_path):
    if os.path.exists(db_path):
        os.remove(db_path)
    con = C.connect(readonly=False)
    con.executescript(DDL)

    logs = sorted(f for f in os.listdir(logdir) if f.endswith(".log"))
    print(f"ingesting {len(logs)} logs from {logdir}", flush=True)

    runs, tptp, stats, flat, tree = [], [], [], [], []
    seen_problems = set()
    t0 = time.time()

    for i, fn in enumerate(logs):
        if i and i % 5000 == 0:
            print(f"  {i}/{len(logs)}  ({time.time()-t0:.0f}s)", flush=True)
        path = os.path.join(logdir, fn)
        problem = C.log_to_problem(fn)
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                text = fh.read()
        except OSError:
            continue

        sc = C.parse_scalars(text)
        froot, frows = C.parse_flat(text)
        troot, trows = C.parse_tree(text)
        clean = 1 if froot is not None else 0
        tree_clean = 1 if troot is not None else 0
        # A signal line means another thread was printing concurrently; even a
        # structurally valid section from such a log is not to be trusted.
        if sc["signal"]:
            clean = tree_clean = 0

        runs.append((
            problem, problem[:3], C.family_of(problem),
            sc["szs"], sc["termination"], sc["time_s"], sc["peak_mb"], sc["instr_M"],
            sc["signal"], sc["user_error"],
            froot[0] if clean else None,
            froot[1] if clean else None,
            troot[0] if tree_clean else None,
            clean, tree_clean,
            None if clean else (frows if froot is None else "signal"),
            None if tree_clean else (trows if troot is None else "signal"),
            len(text),
        ))

        if clean:
            for name, t, a, c, i in frows:
                flat.append((problem, name, t, a, c, i))
        if tree_clean:
            for p, name, d, t, a, c, i, s, si in C.add_self_times(trows):
                tree.append((problem, p, name, d, t, a, c, i, s, si))

        for section, label, proof, total in C.parse_stats(text):
            stats.append((problem, section, label, proof, total))

        if problem not in seen_problems:
            seen_problems.add(problem)
            h = C.parse_tptp_header(C.problem_path(problem))
            if h:
                size = None
                if h["atoms"] is not None:
                    size = h["atoms"] + (h["connectives"] or 0) + (h["variables"] or 0)
                tptp.append((
                    problem, h["spc"], h["dialect"], h["tptp_status"], h["rating"],
                    h["formulae"], h["atoms"], h["equ_atoms"], h["max_formula_atoms"],
                    h["connectives"], h["max_formula_depth"], h["max_term_depth"],
                    h["predicates"], h["functors"], h["symbols"], h["variables"],
                    h["types"], h["type_conns"], size,
                ))

    con.executemany("INSERT INTO runs VALUES (%s)" % ",".join("?" * 18), runs)
    con.executemany("INSERT INTO tptp VALUES (%s)" % ",".join("?" * 19), tptp)
    con.executemany("INSERT INTO stats VALUES (?,?,?,?,?)", stats)
    con.executemany("INSERT INTO nodes_flat VALUES (?,?,?,?,?,?)", flat)
    con.executemany("INSERT INTO nodes_tree VALUES (?,?,?,?,?,?,?,?,?,?)", tree)
    con.execute("INSERT INTO meta VALUES ('logdir', ?)", (os.path.abspath(logdir),))
    con.execute("INSERT INTO meta VALUES ('ingested', ?)", (time.strftime("%F %T"),))
    con.executescript(INDEXES)
    con.executescript(VIEWS)
    con.commit()

    print(f"\ndone in {time.time()-t0:.0f}s")
    report(con)
    con.close()


def report(con):
    q = lambda s, *a: con.execute(s, a).fetchall()  # noqa: E731
    n = q("SELECT COUNT(*) c FROM runs")[0]["c"]
    ok = q("SELECT COUNT(*) c FROM runs WHERE clean=1")[0]["c"]
    tok = q("SELECT COUNT(*) c FROM runs WHERE tree_clean=1")[0]["c"]
    print(f"runs={n}  flat-clean={ok} ({100*ok/n:.1f}%)  tree-clean={tok} ({100*tok/n:.1f}%)")
    print(f"nodes_flat={q('SELECT COUNT(*) c FROM nodes_flat')[0]['c']}  "
          f"nodes_tree={q('SELECT COUNT(*) c FROM nodes_tree')[0]['c']}  "
          f"stats={q('SELECT COUNT(*) c FROM stats')[0]['c']}  "
          f"tptp={q('SELECT COUNT(*) c FROM tptp')[0]['c']}")

    print("\nrejection reasons (flattened profile):")
    for r in q("SELECT COALESCE(reject,'ok') k, COUNT(*) c FROM runs GROUP BY 1 ORDER BY c DESC"):
        print(f"  {r['k']:38s} {r['c']:6d}")

    print("\nreject bias check -- clean rate per dialect x termination:")
    ue = q("SELECT COUNT(*) c FROM runs WHERE user_error IS NOT NULL")[0]["c"]
    print(f"  (excluding {ue} runs that ended in a Vampire user error -- never attempted)")
    rows = q("""SELECT dialect, termination,
                       COUNT(*) n, SUM(clean) ok
                FROM v WHERE user_error IS NULL
                GROUP BY 1,2 HAVING n >= 50 ORDER BY dialect, n DESC""")
    for r in rows:
        pct = 100.0 * (r["ok"] or 0) / r["n"]
        flag = "   <-- low" if pct < 80 else ""
        print(f"  {str(r['dialect']):5s} {str(r['termination'])[:34]:34s} "
              f"{r['n']:6d} {pct:6.1f}%{flag}")


def selftest(db_path):
    """Cross-validate the two independent renderings of the same measurement data."""
    con = C.connect()
    fails = 0

    print("1. flattened == aggregation of the trace tree, per (problem, node)")
    # The two dumps are independent renderings of the same tree, so they must agree
    # exactly -- EXCEPT under `Instruction limit`.  There the timer thread prints while
    # the main thread is still proving (Lib/Timer.cpp limitReached -> statistics->print,
    # then terminateImmediately), so counters grow between the two dumps.  The drift is
    # always in the direction flat > tree and empirically under 2%.
    rows = con.execute("""
        WITH agg AS (
          SELECT problem, node, SUM(total_ns) t, SUM(cnt) c
          FROM nodes_tree GROUP BY problem, node
        )
        SELECT r.termination = 'Instruction limit' AS ilim,
               COUNT(*) n,
               SUM(agg.c IS NULL) missing,
               SUM(agg.c != f.cnt) mism,
               SUM(agg.c > f.cnt) wrong_dir,
               MAX(1.0 * ABS(COALESCE(agg.c, 0) - f.cnt) / MAX(f.cnt, 1)) worst
        FROM nodes_flat f
        JOIN runs r ON r.problem = f.problem AND r.clean = 1 AND r.tree_clean = 1
        LEFT JOIN agg ON agg.problem = f.problem AND agg.node = f.node
        GROUP BY 1
    """).fetchall()
    for r in rows:
        kind = "instruction-limited" if r["ilim"] else "normally terminated"
        if r["ilim"]:
            # Before the timer-thread race was fixed, this bucket drifted on ~8% of
            # rows, always flat>tree: the trace kept being mutated between the two
            # dumps. With the trace frozen before reporting it must now agree
            # exactly, exactly as the normally-terminated bucket does. Any drift
            # reappearing here means the freeze regressed.
            ok = r["missing"] == 0 and r["mism"] == 0
            note = ("exact agreement (trace frozen before reporting)" if ok else
                    f"{r['mism']} rows drift (max {100*(r['worst'] or 0):.2f}%), "
                    f"{r['wrong_dir']} flat>tree -- the reporting race is back")
        else:
            ok = r["missing"] == 0 and r["mism"] == 0
            note = "exact agreement" if ok else f"{r['mism']} mismatches, {r['missing']} missing"
        fails += 0 if ok else 1
        print(f"   {'ok  ' if ok else 'FAIL'} {kind:20s} {r['n']:7d} rows: {note}")

    # In *instructions* rather than nanoseconds. Times are printed rounded to three
    # significant figures, so a root printed as "26 s" hides up to a second and the
    # children can legitimately outsum it by nearly 4%; that made this check a test
    # of the printer's rounding rather than of the data, and it tripped on three
    # ALG problems in the 11156 sweep for exactly that reason. Instruction counts
    # are printed as exact integers, so the invariant is exact and needs no
    # tolerance at all.
    print("2. sum of self instructions <= root total, per run")
    bad = con.execute("""
        SELECT n.problem, SUM(n.self_instr) s, r.root_instr root
        FROM nodes_tree n JOIN runs r USING(problem)
        WHERE r.tree_clean = 1 AND n.self_instr IS NOT NULL AND r.root_instr > 0
        GROUP BY n.problem
        HAVING SUM(n.self_instr) > r.root_instr
        LIMIT 20
    """).fetchall()
    if bad:
        fails += 1
        print("   FAIL: self instructions exceed the root total:")
        for b in bad[:10]:
            print(f"     {b['problem']:22s} self={b['s']} root={b['root']}")
    else:
        print("   ok (no run attributes more exclusive instructions than the root measured)")

    # Re-parse one log straight from disk and compare every row against what the DB
    # stored. Hardcoding a snapshot of one sweep's numbers here would only mean
    # "the sweep has not changed", and would have to be re-hardcoded each time;
    # this checks the thing that actually matters -- that ingestion is faithful --
    # and stays valid across sweeps.
    logdir = con.execute("SELECT value FROM meta WHERE key='logdir'").fetchone()["value"]
    sample = con.execute("""SELECT problem FROM runs WHERE clean = 1
                            ORDER BY problem LIMIT 1""").fetchone()["problem"]
    logname = next(f for f in os.listdir(logdir)
                   if f.endswith(".log") and C.log_to_problem(f) == sample)
    with open(os.path.join(logdir, logname), "rb") as fh:
        text = fh.read().decode("utf-8", "replace")
    _root, rows = C.parse_flat(text)
    print(f"3. re-parse of {sample} agrees with the database ({len(rows)} rows)")
    stored = {r["node"]: (r["total_ns"], r["cnt"], r["instr"]) for r in con.execute(
        "SELECT node, total_ns, cnt, instr FROM nodes_flat WHERE problem=?", (sample,))}
    mismatched = [(name, (t, c, i), stored.get(name))
                  for name, t, _a, c, i in rows if stored.get(name) != (t, c, i)]
    fails += 1 if (mismatched or len(stored) != len(rows)) else 0
    if mismatched:
        print(f"   FAIL {len(mismatched)} rows differ from the log:")
        for name, got, want in mismatched[:5]:
            print(f"     {name:26s} log={got} db={want}")
    elif len(stored) != len(rows):
        print(f"   FAIL row count: log has {len(rows)}, db has {len(stored)}")
    else:
        print("   ok (total_ns, cnt and instr identical on every row)")

    print("4. no unknown node names leaked in")
    bad = con.execute("SELECT DISTINCT node FROM nodes_flat").fetchall()
    unknown = [b["node"] for b in bad if b["node"] not in C.KNOWN_NODES]
    fails += 1 if unknown else 0
    print(f"   {'FAIL: ' + str(unknown[:10]) if unknown else 'ok (%d known names)' % len(bad)}")

    con.close()
    print("\nSELFTEST", "FAILED" if fails else "PASSED")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--logdir", default=C.LOGDIR)
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(selftest(C.DB))
    ingest(a.logdir, C.DB)


if __name__ == "__main__":
    main()

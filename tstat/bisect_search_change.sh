#!/bin/sh
# Which commit between 11279 and 11295 changed the search?
#
# 11279 (248fb8b61) and 11295 (e07474dc1) differ by 16 commits: nine of master's
# (the Map/Set equality split and the FlexibleTail series), three of ours adding
# TIME_TRACE nodes, two merges and a build fix. Between them the solved count went
# 13 986 -> 13 960, net -26, with 96% of runs still bit-identical. This finds out
# which commit is responsible.
#
# It is NOT a git bisect. Bisection assumes one commit flips everything, and with a
# vector of probes over sixteen commits that is exactly what should not be assumed --
# several commits may each move a different subset. So every commit is built and run,
# and the output is a table saying which probe changed where. Sixteen builds is a
# couple of hours; the probes themselves are under a minute per build.
#
#   Run this on the machine the sweeps came from. Timing does not matter (the metric
#   is an activation count under -i, which is deterministic), but the binary has to be
#   built the same way the sweep binaries were.
#
# Usage:  sh tstat/bisect_search_change.sh /path/to/tptp/Problems [outdir]
#
# Output: $outdir/results.csv  -- one row per (commit, problem)
#         $outdir/summary.txt  -- first commit at which each probe's count changes

set -eu

PROBLEMS=${1:?usage: bisect_search_change.sh <TPTP Problems dir> [outdir]}
OUT=${2:-/tmp/tstat-bisect}
REPO=$(cd "$(dirname "$0")/.." && pwd)
PROBES="$REPO/tstat/bisect_probes.txt"

FIRST=248fb8b61   # the 11279 binary
LAST=e07474dc1    # the 11295 binary

# The sweep's own invocation, minus proof output. -tstat on is deliberate: it is what
# the sweeps used, and our three commits only cost anything with it on, so turning it
# off would quietly exclude them from the experiment. -stat full is what prints
# "Activations started"; without it the metric below is silently empty.
VFLAGS="-i 100000 -tstat on -p off -stat full"

mkdir -p "$OUT"
: > "$OUT/results.csv"
echo "commit,subject,problem,activations,termination" >> "$OUT/results.csv"

git -C "$REPO" rev-list --reverse "$FIRST^..$LAST" | while read -r sha; do
  short=$(git -C "$REPO" rev-parse --short=9 "$sha")
  subj=$(git -C "$REPO" log -1 --format=%s "$sha" | tr ',' ';')
  wt="$OUT/wt-$short"
  bd="$OUT/build-$short"

  echo "=== $short  $subj"
  # A worktree per commit keeps the main checkout untouched -- Martin works in it.
  [ -d "$wt" ] || git -C "$REPO" worktree add --detach "$wt" "$sha" >/dev/null
  if [ ! -x "$bd/vampire" ]; then
    mkdir -p "$bd"
    ( cd "$bd" && cmake "$wt" -DCMAKE_BUILD_TYPE=Release -DTIME_PROFILING=ON \
        -DZ3_DIR="$REPO/z3/build" >/dev/null && make -j"$(nproc)" vampire >/dev/null )
  fi

  grep -v '^#' "$PROBES" | while read -r prob exp_first exp_last kind; do
    [ -n "$prob" ] || continue
    fam=$(echo "$prob" | cut -c1-3)
    log="$OUT/$short.$prob.log"
    "$bd/vampire" $VFLAGS "$PROBLEMS/$fam/$prob" > "$log" 2>&1 || true
    # the stats block separates label from value with '|', not ':'
    act=$(sed -n 's/^% Activations started *| *//p' "$log" | tr -d ' ' | tail -1)
    ter=$(sed -n 's/^% Termination reason: *//p' "$log" | tail -1)
    echo "$short,$subj,$prob,${act:-NA},${ter:-NA}" >> "$OUT/results.csv"
  done
done

# --- report -----------------------------------------------------------------------
python3 - "$OUT" "$PROBES" <<'PY' | tee "$OUT/summary.txt"
import csv, sys, collections
out, probes = sys.argv[1], sys.argv[2]
exp = {}
for ln in open(probes):
    if ln.startswith('#') or not ln.strip(): continue
    p, a, b, kind = ln.split()
    exp[p] = (a, b, kind)
rows = list(csv.DictReader(open(f"{out}/results.csv")))
order, seen = [], set()
for r in rows:
    if r['commit'] not in seen:
        seen.add(r['commit']); order.append((r['commit'], r['subject']))
by = collections.defaultdict(dict)
for r in rows:
    by[r['problem']][r['commit']] = r['activations']

first, last = order[0][0], order[-1][0]
print("SANITY -- the ends must reproduce the sweeps, or nothing below means anything.")
bad = 0
for p, (a, b, kind) in exp.items():
    got_f, got_l = by[p].get(first), by[p].get(last)
    ok = (got_f == a) and (got_l == b)
    if not ok:
        bad += 1
        print(f"  MISMATCH {p:14s} expected {a}->{b}, got {got_f}->{got_l}")
print(f"  {len(exp)-bad}/{len(exp)} probes reproduce both endpoints.\n")

print("FIRST COMMIT AT WHICH EACH PROBE'S ACTIVATION COUNT CHANGES")
blame = collections.Counter()
for p, (a, b, kind) in sorted(exp.items()):
    prev, culprit = by[p].get(first), None
    for sha, subj in order[1:]:
        v = by[p].get(sha)
        if v != prev:
            culprit = (sha, subj); break
        prev = v
    if culprit:
        blame[culprit] += 1
        print(f"  {p:14s} [{kind:5s}] {a:>8s} -> {b:>8s}   at {culprit[0]}  {culprit[1][:52]}")
    else:
        print(f"  {p:14s} [{kind:5s}] unchanged across the whole range")
print("\nBLAME COUNT")
for (sha, subj), n in blame.most_common():
    print(f"  {n:3d}  {sha}  {subj}")
PY

echo
echo "worktrees and builds left in $OUT -- remove with: git worktree prune after rm -rf"

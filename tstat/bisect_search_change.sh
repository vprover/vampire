#!/bin/sh
# Which commit between the 11279 and 11295 sweeps changed the search?
#
# Between the two sweep binaries the solved count went 13 986 -> 13 960, net -26,
# with 96% of runs still bit-identical. Sixteen commits separate them, so the sweep
# cannot say which. This does.
#
# It walks the FIRST-PARENT path, which turns sixteen commits into seven steps, each
# one a self-contained unit of blame:
#
#   248fb8b61  11279  the 11279 sweep binary                       <- baseline
#   384446ad5  11283  merge #963+#965: Map/Set equality split
#   71a5da3ed  11291  merge #946: the whole FlexibleTail series
#   4727eb556  11292  ours: per-unit phases in the TPTP parser
#   793b9848c  11293  ours: break codetree subsumption into phases
#   1d67b4228  11294  ours: name the resolvent construction
#   e07474dc1  11295  the 11295 sweep binary (iosfwd build fix)
#
# Note the last four steps isolate our three TIME_TRACE commits one at a time. They
# are a live suspect: under -i, LRS estimates reachable clauses from elapsed
# instructions, so inflating instructions per activation by 0.22% makes it set tighter
# limits and discard more -- a policy change, which can flip a problem that finished
# at half budget. If a step in the middle is implicated instead, drill into that PR's
# individual commits with the same script and a narrower range.
#
# Deliberately not a git bisect: bisection assumes one commit flips everything, and
# several of these may each move a different subset of problems, which a single
# bisect answer would hide.
#
#   Run on the machine the sweeps came from, with a clean working tree. Timing does
#   not matter -- the metric is an activation count under -i, which is deterministic.
#
# Usage:  sh tstat/bisect_search_change.sh <TPTP Problems dir> [outdir] [make -j N]
#
# Output: $OUT/results.csv  -- one row per (commit, problem)
#         $OUT/summary.txt  -- first commit at which each probe's count changes
#
# Binaries land in the repo root as vampire_z3_rel_detached_<count>, where <count> is
# the commit number above -- so they are self-labelling, and 11279 / 11295 are literally
# rebuilds of the two sweep binaries. Remove them afterwards at your leisure.

set -eu

PROBLEMS=${1:?usage: bisect_search_change.sh <TPTP Problems dir> [outdir] [jobs]}
OUT=${2:-/tmp/tstat-bisect}
JOBS=${3:-$(nproc 2>/dev/null || echo 8)}

# Finding the repo, in three ways, because this script deliberately gets copied out of
# it (see the relocation below) and a copy cannot use dirname($0)/.. any more:
#   1. TSTAT_REPO, which the re-exec sets;
#   2. the parent of wherever the script sits, for the normal in-repo invocation;
#   3. failing both, the repo containing the working directory -- so a copy made by
#      hand also works, as long as it is run from inside the checkout.
if [ -n "${TSTAT_REPO:-}" ]; then
  REPO=$TSTAT_REPO
elif git -C "$(dirname "$0")/.." rev-parse --show-toplevel >/dev/null 2>&1; then
  REPO=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)
else
  REPO=$(git rev-parse --show-toplevel)
fi
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)                 # absolute: the build step cd's into $REPO
PROBLEMS=$(cd "$PROBLEMS" && pwd)       # absolute for the same reason

# --- get out of the repo before touching it ---------------------------------------
# Every step checks out a historical commit, and BOTH this script and the probe list
# are tracked files under tstat/ that do not exist in most of them. The probe list
# simply disappears mid-run ("bisect_probes.txt: No such file or directory"), and the
# script is worse: sh reads its own source lazily, so having it replaced underneath
# is a live hazard rather than a clean failure. Copy both somewhere git will not
# touch and carry on from there.
if [ "${TSTAT_RELOCATED:-}" != 1 ]; then
  cp "$REPO/tstat/bisect_probes.txt" "$OUT/probes.txt"
  cp "$0" "$OUT/run.sh"
  TSTAT_REPO="$REPO"; TSTAT_RELOCATED=1
  export TSTAT_REPO TSTAT_RELOCATED
  exec sh "$OUT/run.sh" "$@"
fi
PROBES="$OUT/probes.txt"

# Six of the 28 probes -- SWC393-1, KLE017+1, SEV540+1, SWC014+1, SWC394+1 and
# RNG029-3, the last of them one of the four lost problems -- pull in an Axioms file.
# TPTP::resolveInclude tries the including file's own directory, then $TPTP, then
# --include, then the bare relative path against the working directory. Given an
# absolute problem path the first fails, and the last would look for Axioms/ next to
# the repo root, which happens to work in Martin's checkout (it has the symlink) and
# would not elsewhere. Say it explicitly instead: the TPTP root is the parent of the
# Problems directory we were handed.
TPTPROOT=$(dirname "$PROBLEMS")

FIRST=248fb8b61   # the 11279 binary
LAST=e07474dc1    # the 11295 binary

# The repo-root Makefile hardcodes COMMON_FLAGS = -DVTIME_PROFILING=0, so a plain
# `make vampire_z3_rel` produces a binary that rejects -tstat outright. Override it.
#
# This matters beyond the metric. With VTIME_PROFILING=0 every TIME_TRACE expands to
# {}, so our three commits become literal no-ops and the experiment would quietly
# exclude the very suspects it exists to test -- steps 11292/11293/11294 would be
# indistinguishable from 11291 by construction, and the blame would land on master.
#
# It has to be passed on the command line, not edited into the Makefile: the Makefile
# is tracked, so `git checkout --detach` at the top of each step would revert it to 0
# again. On the command line it applies identically to all seven builds and is
# independent of what any commit in the range contains. It also feeds CONF_ID, so
# these objects live in their own obj/ directory and cannot be confused with, or
# invalidated by, an ordinary VTIME_PROFILING=0 build of the same tree.
MAKE_VARS='COMMON_FLAGS=-DVTIME_PROFILING=1'

# The sweeps' own invocation, minus proof output. -stat full is what prints
# "Activations started"; without it the metric is silently empty.
VFLAGS="-i 100000 -tstat on -p off -stat full --include $TPTPROOT"

cd "$REPO"

if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "working tree has uncommitted changes -- commit or set them aside first."
  echo "(deliberately not stashing: the stash stack is shared with other worktrees.)"
  exit 1
fi

# Come back to wherever we started, however we leave.
WAS=$(git symbolic-ref -q --short HEAD || git rev-parse HEAD)
trap 'git checkout -q "$WAS" 2>/dev/null || true' EXIT INT TERM

: > "$OUT/results.csv"
echo "commit,count,subject,problem,activations,termination" >> "$OUT/results.csv"

# $FIRST is not on master's first-parent chain (it is the tip of the branch that
# 384446ad5 merges), so prepend it explicitly as the baseline.
#
# Then keep only steps that actually *contain* the baseline. Without this filter the
# sequence starts 248fb8b61 (11279) -> 611821e9f (11270), and 11270 predates the
# cheaper-scan work that 11279 has: its tree is not a superset of the baseline's, so
# every probe would "change" there for reasons unrelated to what is being tested and
# the blame table would finger the wrong merge. 611821e9f is an ancestor of
# 384446ad5 anyway, so dropping it loses nothing -- that step just becomes
# "everything master had that cheaper-scan did not, merged in".
#
# Kept in a file and read on fd 3 rather than word-split out of a variable: zsh does
# not split unquoted parameters, so `for c in $SEQ` would silently see one giant word
# if anyone ran this with zsh instead of sh. fd 3 keeps the loop's stdin clear of the
# vampire invocations inside it.
SEQFILE="$OUT/sequence.txt"
: > "$SEQFILE"
{ printf '%s\n' "$FIRST"; git rev-list --first-parent --reverse "$FIRST..$LAST"; } |
while IFS= read -r c; do
  if git merge-base --is-ancestor "$FIRST" "$c"; then
    printf '%s\n' "$c" >> "$SEQFILE"
  fi
done
echo "steps to build:"
while IFS= read -r c <&3; do
  printf '  %s  %-6s %s\n' "$(git rev-parse --short=9 "$c")" \
    "$(git rev-list "$c" --count)" "$(git log -1 --format=%s "$c" | cut -c1-50)"
done 3< "$SEQFILE"

while IFS= read -r sha <&3; do
  short=$(git rev-parse --short=9 "$sha")
  cnt=$(git rev-list "$sha" --count)
  subj=$(git log -1 --format=%s "$sha" | tr ',' ';')
  bin="$REPO/vampire_z3_rel_detached_$cnt"

  echo "=== $short  ($cnt)  $subj"
  git checkout -q --detach "$sha"

  # obj/ is keyed on branch+flags, and every step here is detached with the same
  # flags, so the builds share one object directory and each is incremental. No file
  # is deleted anywhere in this range, so the stale-.d hazard in this build pathway
  # (see CLAUDE.md) does not arise.
  if [ ! -x "$bin" ]; then
    make -j"$JOBS" $MAKE_VARS vampire_z3_rel >"$OUT/$cnt.build.log" 2>&1 \
      || { echo "  BUILD FAILED -- see $OUT/$cnt.build.log"; continue; }
  fi
  [ -x "$bin" ] || { echo "  no binary at $bin -- check $OUT/$cnt.build.log"; continue; }

  # Guard, checked on every step rather than once: a VTIME_PROFILING=0 binary rejects
  # -tstat ("tstat is not a valid short option"), every probe would read NA, and the
  # run would look like a uniform no-change rather than a broken build.
  if "$bin" -tstat on --version 2>&1 | grep -q "not a valid"; then
    echo "  ABORT: $bin was built without VTIME_PROFILING -- see $OUT/$cnt.build.log"
    exit 1
  fi

  grep -v '^#' "$PROBES" | while read -r prob exp_first exp_last kind; do
    [ -n "${prob:-}" ] || continue
    fam=$(echo "$prob" | cut -c1-3)
    log="$OUT/$cnt.$prob.log"
    "$bin" $VFLAGS "$PROBLEMS/$fam/$prob" > "$log" 2>&1 || true
    # the stats block separates label from value with '|', not ':'
    act=$(sed -n 's/^% Activations started *| *//p' "$log" | tr -d ' ' | tail -1)
    ter=$(sed -n 's/^% Termination reason: *//p' "$log" | tail -1)
    echo "$short,$cnt,$subj,$prob,${act:-NA},${ter:-NA}" >> "$OUT/results.csv"
  done
done 3< "$SEQFILE"

git checkout -q "$WAS"

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
if not rows:
    print("no results -- every build failed?"); sys.exit(1)
order, seen = [], set()
for r in rows:
    key = (r['commit'], r['count'], r['subject'])
    if key[0] not in seen:
        seen.add(key[0]); order.append(key)
by = collections.defaultdict(dict)
for r in rows:
    by[r['problem']][r['commit']] = r['activations']

first, last = order[0][0], order[-1][0]
print("SANITY -- the ends must reproduce the sweeps, or nothing below means anything.")
bad = 0
for p, (a, b, kind) in exp.items():
    got_f, got_l = by[p].get(first), by[p].get(last)
    if (got_f, got_l) != (a, b):
        bad += 1
        print(f"  MISMATCH {p:14s} expected {a}->{b}, got {got_f}->{got_l}")
print(f"  {len(exp)-bad}/{len(exp)} probes reproduce both endpoints.\n")

print("FIRST STEP AT WHICH EACH PROBE'S ACTIVATION COUNT CHANGES")
blame = collections.Counter()
for p, (a, b, kind) in sorted(exp.items()):
    prev, culprit = by[p].get(first), None
    for sha, cnt, subj in order[1:]:
        v = by[p].get(sha)
        if v != prev:
            culprit = (cnt, subj); break
        prev = v
    if culprit:
        blame[culprit] += 1
        print(f"  {p:14s} [{kind:5s}] {a:>8s} -> {b:>8s}   at {culprit[0]}  {culprit[1][:50]}")
    else:
        print(f"  {p:14s} [{kind:5s}] unchanged across the whole range")
print("\nBLAME COUNT")
for (cnt, subj), n in blame.most_common():
    print(f"  {n:3d}  {cnt}  {subj}")
PY

echo
echo "binaries left in $REPO as vampire_z3_rel_detached_112*; remove at will."

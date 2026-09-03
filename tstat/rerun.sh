#!/bin/sh
# Reproduce one shortlisted problem locally and diff its profile against the sweep.
#
#   ./rerun.sh SYN986+1.005.p                 # default strategy, 30s
#   ./rerun.sh BIO004+1.p -t 60 --lrs_weight_limit_only on
#   VAMPIRE=../vampire_dbg_master_11132 ./rerun.sh ITP007_5.p
#
# Instruction limiting does not work on macOS, so this bounds with -t.  That means the
# local run stops somewhere else than the server run did: compare the *shape* of the
# profile (which node dominates, cost per call), never the absolute totals.  For a
# deterministic bound use -al instead of -t and check which one actually fired.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
: "${VAMPIRE:=$root/vampire_z3_rel_master_11132}"

[ $# -ge 1 ] || { sed -n '2,12p' "$0"; exit 2; }
prob=$1; shift

case "$prob" in
  /*|./*|../*) path=$prob ;;
  *) path="$root/Problems/$(echo "$prob" | cut -c1-3)/$prob" ;;
esac
[ -f "$path" ] || { echo "no such problem: $path" >&2; exit 1; }

# only add -t if the caller did not pass a bound of their own
bound="-t 30"
for a in "$@"; do case "$a" in -t|--time_limit|-al|--activation_limit) bound="" ;; esac; done

# include() in a TPTP problem is resolved against $TPTP (or the cwd), and only the
# repo root has the Problems/ and Axioms/ symlinks into the TPTP release.
export TPTP="$root"

echo "=== local: $VAMPIRE $bound -tstat on $* $path"
(cd "$root" && "$VAMPIRE" $bound -tstat on "$@" "$path") 2>&1 | tee /tmp/tstat-rerun.$$ \
  | sed -n '/start of flattened/,/end of flattened/p'

echo
echo "=== local scalars"
grep -E "^% (SZS status|Termination reason|Time elapsed|Instructions burned|Peak memory)" \
  /tmp/tstat-rerun.$$ || true
rm -f /tmp/tstat-rerun.$$

echo
echo "=== sweep (server, -i 100000, 120 jobs in parallel): exclusive time per node"
"$here/q.sh" "
  SELECT path,
         printf('%8.1f ms', self_ns/1e6) AS self,
         cnt,
         printf('%8.0f ns', 1.0*self_ns/MAX(cnt,1)) AS per_call
  FROM vtree WHERE problem = '$prob'
  ORDER BY self_ns DESC LIMIT 20;"
"$here/q.sh" "
  SELECT szs, termination, time_s, instr_M, peak_mb, dialect, size
  FROM v WHERE problem = '$prob';"

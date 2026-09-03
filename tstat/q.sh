#!/bin/sh
# Ad-hoc SQL against the ingested sweep.  Views you probably want:
#
#   v      one row per run: problem, dialect, family, size, szs, termination, time_s, ...
#   vflat  flattened profile joined to v, restricted to trustworthy runs
#   vtree  trace tree (with self_ns and dotted `path`) joined to v, trustworthy runs
#
#   ./q.sh "SELECT node, SUM(self_ns)/1e9 s FROM vtree GROUP BY 1 ORDER BY 2 DESC LIMIT 15"
#   ./q.sh -- .schema runs
#
# With no argument, drops into an interactive sqlite3 shell.
set -eu
db="$(cd "$(dirname "$0")" && pwd)/tstat.db"
if [ $# -eq 0 ]; then
  exec sqlite3 -header -column "$db"
fi
if [ "$1" = "--" ]; then
  shift
  exec sqlite3 "$db" "$@"
fi
exec sqlite3 -header -column "$db" "$@"

# Where this stands, and how to pick it back up

Read this first if context was lost. It points at the detail rather than repeating it.

## What's done (branch `martin-tstat`, private for now)

1. **`tstat/`** — a SQLite-backed toolkit for mining a `-tstat on` sweep. `README.md`
   documents the measurement hazards (four of them, each established by probing, not
   assumed); `FINDINGS.md` is the numbered write-up of what the master-11131 sweep
   showed. Start there for substance.
2. **Fixed a real bug**: the timer thread crashed ~1 in 5 instruction-limited runs by
   printing the time trace concurrently with the main thread still mutating it
   (`Debug/TimeProfiling.{hpp,cpp}`, `Lib/Timer.cpp`). This is the one change so far
   that's a clean candidate for master on its own — see below.
3. **Added instruction counters alongside time** in `TIME_TRACE`
   (`Lib/PerfInstructions.hpp`, new). Every node now reports both. Validated on the
   server: reproducible to ~0.005% median (after `setarch -R`, see below) against wall
   time's multi-percent-to-multi-hundred-percent spread on an idle machine. This is the
   second master candidate, but bundle it with the mmap/rdpmc plumbing it depends on —
   see the plan file's argument for why that plumbing isn't worth proposing alone.
4. **Determinism validated, with one open finding.** `tstat/determinism.py` runs a
   fixed problem set under `-al` + `-sa otter` (LRS's limits derive from elapsed time
   and instructions, so under LRS the search itself isn't reproducible — always use
   `otter` for this kind of check) and compares per-node instruction/time spreads
   across repeated runs. Result: **run comparison sweeps under `setarch $(uname -m)
   -R`** — it tightens the median instruction spread ~8x. The residual after that
   (~0.005%) is real nondeterminism in master, not measurement noise, and worth its
   own investigation later (see "Loose ends" below) — but it's small enough not to
   block anything here.

## The sweep in flight

Command (Martin is running this, not us):

```
CPUS=$(lscpu -p=CPU,CORE,SOCKET | grep -v '^#' | awk -F, '!seen[$3","$2]++ {print $1}' | paste -sd,)
taskset -c "$CPUS" setarch $(uname -m) -R \
  ./run_in_parallel_plus_local.sh 64 problemsALLlocal.txt \
  ./run_vampire_free.sh ./vampire_z3_rel_martin-tstat_11142 "-i 100000 -tstat on" \
  /home/sudamar2/tstat/problemsALLlocal_tstat11142_tstat-on_i100K
```

Differences from the master-11131 sweep this replaces:
- TPTP on **local disk**, not NFS — the `parsing` hazard (README.md hazard 2) should be
  gone or much smaller. Worth checking as the first sanity pass on the new data.
- **64 workers pinned one-per-physical-core** via `taskset` on the core list above (2
  sockets x 32 cores, confirmed), not 120 unpinned — the contention hazard (README.md
  hazard 3) should shrink a lot. Check with `rpt_ips.py --spread`; old sweep was
  p90/p10 = 2.58x, expect well under 1.5x now.
- **`setarch -R`** (ASLR off) — for the reproducibility reason above.
- Binary `vampire_z3_rel_martin-tstat_11142` — carries the crash fix and the
  instruction counters. Update `common.py`'s `LOGDIR` (or pass `--logdir`) to the new
  directory when ingesting.

## When the new sweep lands: the plan

1. `cd tstat && ./ingest.py --logdir /path/to/problemsALLlocal_tstat11142_tstat-on_i100K
   && ./ingest.py --selftest` (selftest must still pass — it's sweep-independent).
2. **Reassess every finding in `FINDINGS.md` against the new data before trusting any
   of it.** Specifically:
   - §1 (LRS limit maintenance, 25% of corpus time) — should still hold; re-run
     `rpt_hotspots.py` and compare the percentage.
   - §2 (`Property::scan` on HOL) — should still hold; check `rpt_preproc.py
     --outliers`.
   - §3 (parsing = NFS artifact) — should be **gone or much smaller** now. If it's
     still large, that's itself a finding.
   - §6 (time vs. instructions disagree, `property evaluation` 7x underranked by
     time) — re-derive with the full corpus now that every run carries instruction
     counts, not just the one hand-run example.
   - `rpt_ips.py --spread` — confirm the contention hazard actually shrank.
   - Every `rpt_*.py` script should be re-run with `--metric instructions` once that
     flag exists (see "Still to build" below) rather than relying on time-based
     rankings, per §6's lesson.
3. **Then, one bottleneck at a time**, each as an independent, reviewable unit:
   - Pick the highest-confidence finding (currently LRS cadence, §1).
   - Implement the fix on `martin-tstat` (or a fresh branch off it), small and
     focused.
   - Verify per CLAUDE.md conventions: unit test that fails before / passes after
     where possible, `checks/sanity`, and a `-al`-bounded before/after comparison
     under `setarch -R` (now validated as the right way to compare).
   - **Rebase that one fix's commits onto current master** and prepare it as an
     independent PR — `martin-tstat` stays the private working branch; only the
     cherry-picked/rebased fix goes up. Use `git rebase --onto master <base> <fix-branch>`
     or cherry-pick the specific commits, whichever is cleaner once there's a concrete
     commit range to work with.
   - Repeat for the next finding.
   - The crash fix (`49fb21893`) and the instruction-counter change (`a0b186adf` +
     `115552aaa` + `7e07844fb` + follow-ups) are themselves candidates for this
     treatment — they don't need to wait for the new sweep, since they're already
     verified. Could go up first, independent of any performance finding.

## Still to build (not started)

- `--metric instructions` flag across the `rpt_*.py` reports, so rankings use
  instructions instead of time by default (§6 showed time can mis-rank a node's
  importance by 7x).
- Per-node `ps_per_instr` is already in the `vtree` view (added when instruction
  columns were added) but no report surfaces it yet as a ranked list — that's the
  memory-boundedness detector promised in the original plan.

## Loose ends — worth returning to, not blocking anything

- **The ~0.005% residual nondeterminism that survives `setarch -R`.** Confirmed real
  (statistics blocks identical across runs, only per-node cost differs — the
  signature of a pointer-hashed container, not a logic difference). The `Term::getId()`
  explanation in an earlier draft was **retracted** (commit `0fd1a0575`) after Martin
  correctly objected that address-dependent term creation order would have caused
  visible trouble long before now. Current best guess: a `DefaultHash`-on-`Term*`-or-
  `TermList` container somewhere (see the nondeterminism note in `CLAUDE.md` for the
  general pattern and the fix — `SharedTermHash`/`SharedTermListHash`, id-based).
  **Not yet located.** `hvci` (`Indexing/ClauseVariantIndex.cpp`) was the most
  *exposed* node in the determinism runs but is not itself the source — its own
  container and comparator are content/id-keyed. Finding the actual container is a
  distinct hunt; the instruction counters should make it tractable, because they can
  localise which node's cost moves. Worth doing at some point since CLAUDE.md treats
  this class of bug as one to fix, not to work around.
- **`Instructions burned` is mebi, not mega** (`MEGA = 1 << 20` in `Lib/Timer.cpp`,
  found in `FINDINGS.md` §6). Every `-i N` is really N x 2^20, 4.86% more than its
  label. Harmless for ratios, self-consistent, but the label is wrong. Left alone
  deliberately — fixing it would silently reinterpret every existing `-i` value,
  including whatever's baked into portfolio schedules. Needs an explicit decision
  from Martin, not a unilateral fix.
- **`HWV114-1.p`** in `determinism.py`'s default problem set has only 14 nodes above
  the 1ms floor, so its time column is noisy on every run (was 49.7% median once,
  1.6% another time) for reasons unrelated to anything being tested. Either raise its
  `-al` or swap it out; flagged, not fixed.

## Files to read, in order, for a cold start

1. This file.
2. `tstat/README.md` — the four (five, with instruction counters) measurement hazards,
   each with a reproducer.
3. `tstat/FINDINGS.md` — numbered findings against the old sweep; §6 and the ASLR note
   are the most recent and most load-bearing.
4. `git log --oneline` on `martin-tstat` from `d1e247b5e` (the merge-base with master)
   forward — every commit message is written to stand alone.

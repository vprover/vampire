# Where this stands, and how to pick it back up

Read this first if context was lost. It points at the detail rather than repeating it.

## What's done (branch `martin-tstat`, private for now)

1. **`tstat/`** — a SQLite-backed toolkit for mining a `-tstat on` sweep. `README.md`
   documents the measurement hazards; `FINDINGS.md` is the numbered write-up against the
   **11142 sweep**. Start there for substance.
2. **Fixed a real bug**: the timer thread crashed ~1 in 5 instruction-limited runs by
   printing the time trace concurrently with the main thread still mutating it
   (`Debug/TimeProfiling.{hpp,cpp}`, `Lib/Timer.cpp`). **Verified fixed on the new sweep**
   — 2 450 crashes → 0, 0 mangled logs, 100.0% clean in every dialect × termination
   bucket, and 0 counter drift across all 431 645 instruction-limited rows.
3. **Added instruction counters alongside time** in `TIME_TRACE`
   (`Lib/PerfInstructions.hpp`, new). Cross-validated on the new sweep against the
   statistics block's independent `read()` path: ratio 1.0000 at p10/p50/p90 over 11 975
   runs.
4. **The whole toolkit now measures in instructions**, with `--metric time` for the old
   view — see `FINDINGS.md` §6 for why that was necessary rather than cosmetic.

Both prover changes are verified and are clean candidates for master on their own,
independent of any performance finding. They have not been proposed yet.

## The 11142 sweep: goals met

The sweep was run specifically to fix the 11131 sweep's data-quality problems. All of
them are fixed:

| goal | 11131 | 11142 |
|---|---|---|
| crashed runs | 2 450 | **0** |
| logs dropped as mangled | 2 952 of 26 504 | **0** |
| usable runs | 23 750 | **26 265** |
| dialect × termination clean rate | TH0 53%, TH1 27% at `-i` | **100.0% everywhere** |
| tree/flat counter drift under `-i` | 8% of rows | **0 of 431 645** |
| `parsing`, `SET044+1.p` | 113 ms (NFS) | **212 µs** |
| median throughput | 3 126 M instr/s | **5 327** (1.70x) |
| per-node instruction counts | absent | present on all 26 265 |

The one thing that did *not* improve is the cross-run wall-clock spread (2.58x → 2.50x),
and `FINDINGS.md` §7 explains why that was the wrong thing to expect: the metric compares
different problems, so it mixes machine load with genuine memory-boundedness.

## Next: one bottleneck at a time

Each as an independent, reviewable unit:

- Pick the finding. **Ranked by confidence and size, the order is §1 (LRS cadence),
  §2 (`SortHelper::getArgSort` rebuilding the type substitution per argument), then §3
  (parsing cost per atom, which first needs finer `TIME_TRACE` scopes in
  `Parse/TPTP.cpp` before anything can be optimised).**
- Implement on `martin-tstat` (or a fresh branch off it), small and focused.
- Verify per `CLAUDE.md`: a unit test that fails before and passes after where possible,
  `checks/sanity`, and an `-al`-bounded before/after under `setarch -R`.
- **Rebase that one fix's commits onto current master** and prepare it as an independent
  PR. `martin-tstat` stays the private working branch. `git rebase --onto master <base>
  <fix-branch>`, or cherry-pick, whichever is cleaner for the actual commit range.
- Repeat.

Note for §1: the fix is a policy change in `LRS::shouldUpdateLimits()`
(`Saturation/LRS.cpp:57`) and touches no data structure. Because the node is memory-bound,
judge it on wall time as well as instructions — the instruction share understates the win.

## Still to build (not started)

- **Calibrate the instrumentation constant.** Overhead is a fixed number of instructions
  per scope, so it can be *subtracted* (`true = measured − k·cnt`) rather than merely
  flagged. The sweep bounds it at ≤107 instructions/scope; measuring `k` exactly needs
  `calib_overhead.py` extended to read the counter and re-run on the sweep machine. That
  is what would make the fine-grained nodes (`term sharing`, `clause generation`)
  trustworthy for the first time.
- Finer `TIME_TRACE` scopes inside `Parse/TPTP.cpp`, without which §3 cannot be localised.
- `rpt_peers.py` still ranks by time; it is the one report without `--metric`.

## Loose ends — worth returning to, not blocking anything

- **The ~0.005% residual nondeterminism that survives `setarch -R`.** Confirmed real
  (statistics blocks identical across runs, only per-node cost differs — the signature of
  a pointer-hashed container, not a logic difference). The `Term::getId()` explanation in
  an earlier draft was **retracted** (commit `0fd1a0575`) after Martin correctly objected
  that address-dependent term creation order would have caused visible trouble long
  before now. Current best guess: a `DefaultHash`-on-`Term*`-or-`TermList` container
  somewhere (see the nondeterminism note in `CLAUDE.md` for the pattern and the fix —
  `SharedTermHash`/`SharedTermListHash`, id-based). **Not yet located.** `hvci`
  (`Indexing/ClauseVariantIndex.cpp`) was the most *exposed* node but is not the source;
  its own container and comparator are content/id-keyed.
- **`Instructions burned` is mebi, not mega** (`MEGA = 1 << 20` in `Lib/Timer.cpp`).
  Every `-i N` is really N × 2^20, 4.86% more than its label. Harmless for ratios and
  self-consistent, but wrong. Left alone deliberately: fixing it would silently
  reinterpret every existing `-i` value, including those baked into portfolio schedules.
  Needs an explicit decision from Martin.
- **`static unsigned cnt` in `LRS::shouldUpdateLimits()`** — function-local static holding
  per-problem state, which `CLAUDE.md` flags as a hazard. Noticed while investigating §1;
  worth cleaning up if that function is touched anyway.
- **`HWV114-1.p`** in `determinism.py`'s default set has only 14 nodes above the 1 ms
  floor, so its time column is noisy for reasons unrelated to anything being tested.
  Either raise its `-al` or swap it out.

## Files to read, in order, for a cold start

1. This file.
2. `tstat/README.md` — the two live measurement hazards and the two the new sweep removed.
3. `tstat/FINDINGS.md` — eight numbered findings against the 11142 sweep.
4. `git log --oneline` on `martin-tstat` from `d1e247b5e` (the merge-base with master)
   forward — every commit message is written to stand alone.

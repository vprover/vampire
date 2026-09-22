# Where this stands, and how to pick it back up

Read this first if context was lost. It points at the detail rather than repeating it.

## The short version

`tstat/` is a SQLite-backed toolkit for mining a `-tstat on` sweep of all of TPTP.
`README.md` documents the measurement hazards; `FINDINGS.md` is the write-up. The
standing reference is the **11279** sweep (`problemsALLlocal_cheaper11279_tstat-on_i100K`,
commit `248fb8b61`, 26 273 usable runs), and `tstat.db` / `common.py`'s `LOGDIR` point
at it. `FINDINGS.md` §18 indexes every sweep and says which older databases still matter.

**`FINDINGS.md` is organised so you do not have to read it in order:** Part I is the open
work ranked, Part II is how not to fool yourself with the numbers, Part III is history —
each change that has landed, with the sweep pair that measured it.

## What has landed

Everything the first four rounds of this work produced is now on master:

- the **timer-thread trace race** fix — 2 450 crashed runs → 0 (`FINDINGS.md` §17);
- **instruction counters in `TIME_TRACE`** (`Lib/PerfInstructions.hpp`), cross-validated
  against the statistics block's independent `read()` path;
- the **LRS maintenance budget** — 6.57% → 0.95% of corpus instructions, and under
  `-t 60` 26 hours of wall clock moved from overhead into inference (§13);
- the **instrumentation commits** that closed the blind spots — `forward simplification`
  self 19.01% → 0.61%, and with them the two largest findings in the file (§14);
- **`Do not run DistinctGroupExpansion on higher-order problems`**, which fixed a master
  defect that aborted essentially all higher-order input (§15c).

Master's own "cheaper scan" work (§16) then took `Property::scan` down 78.6% and, as a
side effect nobody was aiming at, made `boolean simplification` 2.8x cheaper per call.

## Next: one bottleneck at a time

Ranked in `FINDINGS.md` Part I. By tractability rather than size, the order to pick from:

0. **Run a sweep with the twelve new nodes.** The branch now breaks §1's and §2's two
   largest targets into phases, splits codetree index maintenance into insert and remove,
   and names resolution's resolvent construction (§9, §10). Nothing in `FINDINGS.md` is
   measured with them yet, and between them they divide three of the four largest figures
   in the profile — `resolution` 21.5%, `codetree forward subsumption` 17.8%, `parsing`
   in its per-run tail. Everything below is easier to prioritise afterwards. They cost
   ~0.25% of corpus, almost all of it the two per-`perform` scopes in the code-tree
   matcher; the sweep should confirm that against 11279 at equal effort, the way §15 did
   (0.2% predicted, 0.04% measured).

   §10 lists what would still be unattributed afterwards, with the cost of one more scope
   in each as a share of that node — the number that decides whether a split is worth
   making. `superposition`'s subterm enumeration is the cheapest thing left on it by a
   wide margin (~0.02%) and is worth adding *before* the sweep runs if there is time,
   since adding it later costs a whole sweep.
1. **§4, `interpreted evaluation` on TF0 arithmetic.** Small, self-contained,
   reproducible in seconds: six 42-byte `SWX14x_1.p` problems burn 97% of a full budget
   at 4.66 M instructions per evaluation call, agreeing to within 0.01% of each other.
   One root cause, not six. A good first problem for someone cold, and it does not need
   the new sweep.
2. **§3, `BetaEtaSimplify`.** `SYN007^4.014.p` spends its entire 104.9 G budget in **one
   call**. Bug-shaped rather than tuning-shaped, and confined to TH0/TH1.
3. **§1, `codetree forward subsumption`.** The largest target in the file — 17.79% of
   everything, with single calls costing 2.75 G instructions on the GRA family. The local
   reading on `GRA124-1.p` already says ~93% of it is the code-tree interpreter itself
   rather than the multi-literal matching, which is the hard answer: there is no phase to
   peel off, only the interpreter to make cheaper or to enter less often. Worth checking
   whether the ordering heuristic at insertion (`codetree literal ordering`, 59% of
   insertion on GRA) is what makes the tree so expensive to walk.
4. **§2, `parsing`.** 20% of the corpus gives it at least a fifth of its budget and 54
   runs never start saturating. Locally, ~87% of it is neither per-unit finalisation nor
   the include machinery — so it is the lexer, the state machine, or term and formula
   construction, and the sweep's instructions-per-input-byte will say which is even
   possible.
5. **§5, LRS as a *time* problem.** The instruction share is finished; what survives the
   cap runs at 6x the corpus stall rate and is still 6% of wall clock. The open decision
   is whether the budget should be applied in the time unit regardless of which limit
   binds — see the end of §5.

For each: implement on `martin-tstat` (or a fresh branch off it), small and focused;
verify per `CLAUDE.md` (a unit test that fails before and passes after where possible,
`checks/sanity` against a **release** build, and an `-al`-bounded before/after under
`setarch -R`); then rebase that one fix's commits onto current master as an independent
PR. `martin-tstat` stays the working branch.

## Still to build (not started)

- **Calibrate the instrumentation constant.** Overhead is a fixed number of instructions
  per scope, so it can be *subtracted* (`true = measured − k·cnt`) rather than merely
  flagged. The sweep bounds it at ≤107 instructions/scope; measuring `k` exactly needs
  `calib_overhead.py` extended to read the counter and re-run on the sweep machine. That
  is what would make the fine-grained nodes (`term sharing`, `clause generation`)
  trustworthy for the first time.
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
  its own container and comparator are content/id-keyed. Note that master has since
  removed `DefaultHash` entirely (`b17f08e7c`), which may have closed this by accident —
  worth re-running `determinism.py` before spending time on it.
- **`Instructions burned` is mebi, not mega** (`MEGA = 1 << 20` in `Lib/Timer.cpp`).
  Every `-i N` is really N × 2^20, 4.86% more than its label. Harmless for ratios and
  self-consistent, but wrong. Left alone deliberately: fixing it would silently
  reinterpret every existing `-i` value, including those baked into portfolio schedules.
  Needs an explicit decision from Martin.
- **The sweep profiles no FMB at all.** Every run in it is the default saturation mode, so
  `-sa fmb` is a hole in the corpus, not just in the findings. Two consequences: the four
  `fmb *` nodes added in "Time profiling: close the remaining FMB gaps" have never been
  exercised by a sweep, and `minisat eliminate var` / `minisat bwd subsumption check`
  (`Minisat/simp/SimpSolver.cc`) look dead but are not — `SimpSolver` is reachable only
  through `MinisatInterfacingNewSimp`, whose one instantiation is
  `FMB/FiniteModelBuilder.cpp:247`, so those two sites fire under `-sa fmb` and nowhere
  else. Worth a small targeted `-sa fmb` sweep over the satisfiable end of TPTP rather
  than folding FMB into the main one, whose point is the default path.
- **`symbol counts` is the NUM`^4` family's new largest pre-saturation cost** (~7% of the
  run, down from `property evaluation`'s 89%). Much smaller than what it replaced, but it
  is now the visible one, and it is a single pass over the clauses at
  `PrecedenceOrdering` construction (`Kernel/SymbolUsage.cpp`).
- **`HWV114-1.p`** in `determinism.py`'s default set has only 14 nodes above the 1 ms
  floor, so its time column is noisy for reasons unrelated to anything being tested.
  Either raise its `-al` or swap it out.

## Files to read, in order, for a cold start

1. This file.
2. `tstat/README.md` — the live measurement hazards and the ones past sweeps removed.
3. `tstat/FINDINGS.md` — Part I if you want work to do, Part III if you want to know why
   things are the way they are.
4. `git log --oneline` on `martin-tstat` from its merge-base with master forward — every
   commit message is written to stand alone.

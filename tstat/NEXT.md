# Where this stands, and how to pick it back up

Read this first if context was lost. It points at the detail rather than repeating it.

## The short version

`tstat/` is a SQLite-backed toolkit for mining a `-tstat on` sweep of all of TPTP.
`README.md` documents the measurement hazards; `FINDINGS.md` is the write-up. The
standing reference is the **11295** sweep (`problemsALLlocal_tprofile11295_tstat-on_i100K`,
commit `e07474dc1`, 26 273 usable runs, 78 node names), and `tstat.db` / `common.py`'s
`LOGDIR` point at it. `FINDINGS.md` §20 indexes every sweep and says which older
databases still matter; §19 is what 11295 cost and what else moved in it.

**`FINDINGS.md` is organised so you do not have to read it in order:** Part I is the open
work ranked, Part II is how not to fool yourself with the numbers, Part III is history —
each change that has landed, with the sweep pair that measured it.

## What has landed

Everything the first four rounds of this work produced is now on master:

- the **timer-thread trace race** fix — 2 450 crashed runs → 0 (`FINDINGS.md` §18);
- **instruction counters in `TIME_TRACE`** (`Lib/PerfInstructions.hpp`), cross-validated
  against the statistics block's independent `read()` path;
- the **LRS maintenance budget** — 6.57% → 0.95% of corpus instructions, and under
  `-t 60` 26 hours of wall clock moved from overhead into inference (§14);
- the **instrumentation commits** that closed the blind spots — `forward simplification`
  self 19.01% → 0.61%, and with them the two largest findings in the file (§15);
- **`Do not run DistinctGroupExpansion on higher-order problems`**, which fixed a master
  defect that aborted essentially all higher-order input (§16c).

Master's own "cheaper scan" work (§17) then took `Property::scan` down 78.6% and, as a
side effect nobody was aiming at, made `boolean simplification` 2.8x cheaper per call.

The **phase breakdown** — twelve nodes splitting §1, §2, §9 and §10's largest figures —
is in too, and 11295 measured it (§19): median −0.22% of work done, net −26 problems,
zero soundness contradictions. What it showed is in the ranking below.

## Next: one bottleneck at a time

Ranked in `FINDINGS.md` Part I. By tractability rather than size, the order to pick from:

1. **§1, the multi-literal matching blow-up.** The split delivered the one clearly
   bug-shaped thing in the file. `ClauseMatcher::matchGlobalVars` /
   `existsCompatibleMatch` is a backtracking search over combinations of per-literal
   matches with no bound, and on `ANA073^1.p` it spends **33 million instructions
   deciding one subsumption**; 68% of the whole node is in 172 runs, almost all TH0
   (QUA, ITP, ANA, SEU). Bounded, concentrated, and a cap or a better match-vector
   ordering is a contained change. Start here.
2. **§9, `codetree literal ordering`.** 8.12 T, **0.61% of the corpus on its own** —
   five times the entire cost of index *removal*, and more than `splitting`. It is a
   quadratic greedy heuristic that compiles every literal once to run its `evalSharing`
   walks and then `codetree code compilation` compiles them all again: ~15 T, 1.1% of
   corpus, spent deciding and re-deciding how to lay a clause into the tree. The
   redundant first compilation is the obvious thing to look at, and it is self-contained.
3. **§4, `interpreted evaluation` on TF0 arithmetic.** Six `SWX14x_1.p` problems burn
   97% of a full budget at **4.66 M instructions per evaluation call**, agreeing to
   within 0.01% of each other — one root cause, not six. Self-contained and reproducible
   in seconds. The problems are *not* small (167 KB files); what is extreme is term
   depth, 77 against a corpus median of 4, so the open question is whether 4.66 M per
   call is a defect or the price of normalising an expression that size.
4. **§3, `BetaEtaSimplify`.** `SYN007^4.014.p` spends its entire 104.9 G budget in **one
   call**. Bug-shaped rather than tuning-shaped, and confined to TH0/TH1.
5. **§10, instrument `Indexing/SubstitutionTree` retrieval.** The sweep promoted this to
   the biggest unmeasured thing in the prover: `resolution` self *is* retrieval and
   `superposition` self is retrieval plus enumeration, so **~31% of the corpus** is
   looking clauses up. No scope anywhere in it. The cheap way in is scoping
   `EqHelper::getSubtermIterator` and taking retrieval by subtraction, but its cost
   depends on candidates per subterm and is unmeasured — and measure it on
   **budget-bound** runs, not short local ones, which is exactly how the
   `perform resolution` estimate came out 7x low (§19).
6. **§5, LRS as a *time* problem.** The instruction share is finished; what survives the
   cap runs at 6x the corpus stall rate and is still 6% of wall clock. The open decision
   is whether the budget should be applied in the time unit regardless of which limit
   binds — see the end of §5.

**Not on this list any more:** §2 `parsing`. The breakdown ruled out everything it could
name — per-unit finalisation 5%, closure check 2%, `include` 0.03% — leaving 93% in the
state machine and term/formula construction, which has no per-unit boundary to scope.
The next step there is a `perf record` on `HWV133-1.p`, not another sweep node.

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

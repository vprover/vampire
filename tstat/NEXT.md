# Where this stands, and how to pick it back up

Read this first if context was lost. It points at the detail rather than repeating it.

## The short version

`tstat/` is a SQLite-backed toolkit for mining a `-tstat on` sweep of all of TPTP.
`README.md` documents the measurement hazards; `FINDINGS.md` is the write-up. The
standing reference is the **11304** sweep
(`problemsALLlocal_interpreted11304_otter_tstat-on_i100K`, commit `a7dff21ad`, 26 272
usable runs, 77 node names), and `tstat.db` / `common.py`'s `LOGDIR` point at it.
`FINDINGS.md` §20 indexes every sweep and says which older databases still matter.

**11304 is the first sweep under `-sa otter`, and that is the new standing regime.** LRS
estimates its limits from elapsed instructions, so under it the instrumentation was a
*policy* change and not merely a cost — §21 measures that costing 25 solved problems, and
§12 is the rule that came out of it. Otter has no such feedback loop. The price is 486
fewer problems solved and a corpus that reallocates hugely (§1: 14.95% → 43.28%), so
**nothing in an otter sweep may be compared against an LRS one** — §12 again.

**We follow master from here.** Each sweep is taken on master or on a branch about to
land, and does double duty: catching performance regressions nothing else would catch,
and checking whether the optimizations these findings motivate actually pay. §14, §17 and
§22 are three that did.

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
is in too (merged as `2d474c360`), and 11295 measured it (§19): median −0.22% of work
done, net −26 problems, zero soundness contradictions. The 11291 control sweep attributes
−25 of those −26 to the instrumentation itself, via LRS reading the overhead as a reason
to tighten its limits (§21) — a fact about the measuring instrument, not about the
prover, since shipped builds compile `TIME_TRACE` to nothing. **Do not compare solved
counts across sweeps with different node sets** (§12).

And **§4 is fixed** (§22): three commits on `BottomUpTermTransformer` and the interpreted
evaluators took `interpreted evaluation` from 0.87% of corpus to 0.13%, from 117 runs
giving it over a fifth of their budget to **2**, and by **1 072x–2 500x** per call on the
six `SWX` problems the section was built around. That is the third finding in this file
to turn into a landed optimization.

## Next: one bottleneck at a time

Ranked in `FINDINGS.md` Part I. By tractability rather than size, the order to pick from:

0. **§1 is now 43% of the corpus.** Under otter, `codetree forward subsumption` is bigger
   than the next six nodes combined and dominates over half of 6 225 runs. Everything
   below it is a rounding error by comparison. It splits into two unrelated problems:

   1. **The multi-literal matching blow-up** — the one clearly bug-shaped thing in the
      file, and it *survived the regime change intact*, which is the best evidence it is
      real rather than an artefact of LRS's clause population.
      `ClauseMatcher::matchGlobalVars` / `existsCompatibleMatch` is a backtracking search
      over combinations of per-literal matches with no bound; on `GRA071^2.p` it spends
      **6.5 billion instructions deciding one subsumption**, in twelve calls, and 131
      runs still give it more than half their budget. Bounded, concentrated, and a cap or
      a better match-vector ordering is a contained change. **Start here.**
   2. **The interpreter**, now 89% of the subtree. Far larger but with no pathology to
      aim at — it is spread over 25 000 runs and `Matcher::execute` is a bytecode
      dispatch loop that should not be entered with a scope. If §1.1 is exhausted, the
      question to ask about §1.2 is algorithmic (are we checking too many candidates?),
      not micro-optimizing (is the loop tight?).

2. **§9, `codetree literal ordering`.** Now **2.07% of corpus** under otter, up from
   0.61% — a quadratic greedy heuristic that compiles every literal once to run its
   `evalSharing` walks, after which `codetree code compilation` (1.64%) compiles them all
   again. Between them 3.7% of the corpus goes on deciding and re-deciding how to lay a
   clause into the tree. The redundant first compilation is the obvious thing to look at,
   and it is self-contained.
3. **§3, `BetaEtaSimplify`.** `SYN007^4.014.p` spends its entire 104.9 G budget in **one
   call**; 242 runs give the node more than half their budget. Bug-shaped rather than
   tuning-shaped, and confined to TH0/TH1.
4. **§7, `forward demodulation`** — 11.04% of corpus under otter against 2.85% under LRS,
   and second in the table. Nothing has been looked at here since §7 checked the folklore;
   it deserves a fresh read at its new weight.
5. **§10, instrument `Indexing/SubstitutionTree` retrieval.** Still the biggest
   unmeasured thing, but **the otter sweep cut the estimate of its size sharply**: the
   "~31% of corpus" figure came from `resolution` and `superposition` self time under
   LRS, and most of that was LRS rejecting candidates inside the generation iterator
   (§19), not retrieval. Those nodes are now 1.93% and 3.51%. Re-estimate before
   investing: the cheap way in is scoping `EqHelper::getSubtermIterator` and taking
   retrieval by subtraction.
6. **§4's residual, `SWW838_1.p`.** The interpreted-evaluation fix reached everything
   except this one problem: 843 485 instructions per call, unchanged by a factor of 1.01,
   still 93.5% of its own run. One instance in the corpus, so low priority — but it is a
   *different* mechanism from the one just fixed, and it is precisely localised.

**Before any of that: one SIGSEGV.** `SWV645_5.p` crashes after 61.5 G instructions,
well under budget — the only crash in 26 504 runs and the first since §18's reporting
race was fixed. The trace printed completely first, so it is not that fault returning.
It is either the otter regime or the three interpreted-evaluation commits, and the latter
are exactly the kind of change (`BottomUpTermTransformer` no longer rebuilding subterms,
numerals no longer copied) where a lifetime mistake looks like this. §22 has the
reproducer and the discriminating run. A crash outranks a profiling target.

**Not on this list any more:**

- **§2 `parsing`.** The breakdown ruled out everything it could name — per-unit
  finalisation 5%, closure check 2%, `include` 0.03% — leaving 93% in the state machine
  and term/formula construction, which has no per-unit boundary to scope. The next step
  there is a `perf record` on `HWV133-1.p`, not another sweep node.
- **§4 `interpreted evaluation`.** Fixed (§22). Only the `SWW838_1.p` residual above.
- **§5, LRS as a *time* problem.** Not dropped so much as unmeasurable here: the node
  fires in 0 of 11304's runs because otter has no LRS. The finding stands for LRS, which
  is still Vampire's default strategy and so still what users run — re-measure it on
  `tstat-11295.db` or the `-t 60` pair, not on the standing sweep.

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

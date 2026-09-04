# Findings from the 11142 sweep

`vampire_z3_rel_martin-tstat_11142 -i 100000 -tstat on`, 26 504 TPTP problems, TPTP on
local disk, 64 workers pinned one per physical core, ASLR off. **26 265 usable runs**
(the other 239 are Vampire user errors that never reached profiling), 247 671 s and
1 338 T instructions of exclusive cost.

> **§1 has since been acted on.** The 11156 sweep is the same configuration with the LRS
> maintenance cap in place at its default `-lmb 0.05`. What it did is written up in §9 at
> the end of this file; §1 below is left as the diagnosis that motivated the change.

Read `README.md` first for how to read these numbers. This sweep replaces the
master-11131 one; where a finding changed, the old claim is stated so the difference is
visible rather than silently overwritten.

**Cost is counted in instructions unless stated otherwise.** That is not cosmetic: time
and instructions rank the nodes differently by up to 3x, and §6 is about exactly that.

---

## 1. `LRS limit maintenance`: 6.6% of the work, 19.4% of the wall clock

**Revised, not merely confirmed.** The old sweep called this "25% of all time" and made
it the clear top target. In instructions it is much smaller, and the gap is itself the
finding.

`./rpt_hotspots.py` — 87 914 G instructions, **6.57% of corpus**, against **19.44% of
corpus self time**: a `t/i` of **2.96x**, the largest of any node. At **548 ps/instr**
against a corpus average of 185 it is the most memory-bound node in the prover
(`./rpt_hotspots.py --metric membound` ranks it first). It is not executing much code;
it is walking a large structure and missing cache.

Per run (13 186 runs with at least 200 updates):

```
share of the run's instructions   median  5.0%   p90 18.0%   max 64.3%
share of the run's time           median 11.5%   p90 37.2%   max 90.0%
```

**Mechanism, unchanged and confirmed in the source.** `LRS::poppedFromUnprocessed`
(`Saturation/LRS.cpp:41`) calls `_passive->updateLimits()`, which
(`Saturation/ClauseContainer.cpp:60`) runs a *full simulation*: `simulationInit()` then
`simulationPopSelected()` repeated `estReachableCnt` times.

**The cadence is far tighter than the constants suggest, which is the part worth
knowing.** `LRS::shouldUpdateLimits()` (`Saturation/LRS.cpp:57`) fires when its own call
counter hits 500, or **50** once limits are active. Those read like "every 500 / every 50
activations" — but the counter advances once per clause *popped from unprocessed*, and a
single activation pushes many clauses through unprocessed. Measured:

```
activations per limit update   median 1.4    p10 0.2    p90 11.0
```

So in the median run a full passive-set simulation runs **more often than once per
activation**, and at p10 five times per activation. That is roughly 36x more often than
reading the constant as activations would suggest.

Cost per update against the run's passive size:

```
passive ~   2 198   median   23 k instr/call     6 us
passive ~   9 774   median   88 k                29 us
passive ~  42 446   median  391 k               141 us
passive ~ 105 618   median  784 k               356 us
passive ~ 393 752   median  920 k               411 us
```

Roughly linear to ~10^5 (slope 0.91 over the first four buckets) then flattening, because
`estReachableCnt` bounds the simulation once passive is very large. The old sweep's clean
"slope 1.01" was fitted on bucket medians only; over all 13 186 raw points the exponent is
0.74 in instructions and 0.90 in time, r = 0.53 / 0.61.

**Fix**: make the cadence in `shouldUpdateLimits()` adaptive — keep measured limit
maintenance under a fixed fraction of elapsed work, or scale the interval with
`sizeEstimate()` — instead of the constants 500/50. Purely a policy change, no data
structure touched. Because the node is memory-bound, the wall-clock win should exceed the
6.6% instruction share; on a loaded machine it should exceed it by more.

Worth noting while in this function: `static unsigned cnt=0;` is a function-local static
holding per-problem state, which `CLAUDE.md` calls out as a hazard rather than an
optimisation.

**Worst runs** (`./rpt_peers.py` ranks the same set independently): the whole `SYN903-1`
to `SYN912-1` group at 54-64% of instructions, `HWV121-1.p` 49.8%, `CSR114+15.p` 49.6%,
`CSR066+4.p` 48.8%, `LCL684+1.005.p` 46.5%, and the `ITP2xx_3` (TX0) / `ITP0xx_5` (TF0)
families at 62-77% of main-loop time against peer medians of 3-5%.

---

## 2. `Property::scan` is up to 88% of a HOL run — confirmed, and larger than before

`./rpt_preproc.py --outliers`, and directly:

```
NUM795^4.p  property evaluation  2 calls   93 G instr = 88% of the whole run  (7.6 s)
NUM796^4.p                       2 calls   93 G       = 88%
NUM793^4.p                       2 calls   79 G       = 75%
NUM789^4.p                       2 calls   72 G       = 68%
... the whole NUM76x-NUM79x^4 family, 15+ problems
```

All of them then hit the instruction limit — the budget is spent before saturation gets
anywhere. Corpus-wide `property evaluation` is only 0.816% of instructions (10 T over
67 452 calls), so this is concentrated, not pervasive; but where it bites, it consumes the
run. By dialect the mean share is 3% on TH0/TX1 against 1% on FOF/CNF.

**Mechanism, verified in the source.** `Property::scan(Literal*)`
(`Shell/Property.cpp:605`) does

```cpp
for (int i=0; i<arity; i++) { scanSort(SortHelper::getArgSort(lit, i)); }
```

and `SortHelper::getArgSort` (`Kernel/SortHelper.cpp:217`) builds a fresh `Substitution`
and calls `getTypeSub(t, subst)` — which binds *every* type argument
(`Kernel/SortHelper.cpp:68`) — before applying it to the one argument asked for. Scanning
a term of arity n therefore costs n substitution builds instead of one. In HOL every `@`
is polymorphic, so this is the whole traversal.

**Two independent fixes, both small:**

- a bulk `SortHelper::getArgSorts(const Term*, Stack<TermList>&)` that calls `getTypeSub`
  once and applies it to each `ot->arg(i)`. `Shell/Property.cpp:605` and `:715` are the
  hot callers, and the same `for i < arity: getArgSort(t, i)` pattern appears in ~10
  further places (`Shell/BlockedClauseElimination.cpp:477`,
  `Inferences/TheoryInstAndSimp.cpp:134,209`, `Indexing/AcyclicityIndex.cpp:71,84`,
  `Inferences/TermAlgebraReasoning.cpp:384,397`, ...), so one helper fixes all of them.
- find out why the scan runs more than once. Call counts are now 1 (21 681 rows), 2
  (21 039) and 3 (1 231) — the old sweep's "4 times" no longer reproduces, but 2 scans of
  a HOL problem still costs seconds. Per `CLAUDE.md` the `Problem` property cache is
  invalidated by transformations and silently repaired by the next `getProperty()`.

---

## 3. Parsing costs 5 800 - 33 800 instructions per input atom

**This finding is new, and it replaces the old §3.** In the 11131 sweep `parsing`
measured the server's NFS mount rather than the parser, so the whole node was written off
as an artifact. With TPTP on local disk the artifact is gone (`SET044+1.p`: 113 ms then,
**212 µs** now) and what is left is real — and was never previously visible.

`./rpt_preproc.py --fit --node parsing` — cleanly **linear** in input size in every
dialect (FOF b = 1.03 [1.01, 1.04]), so there is no scaling bug. The constant is the
issue:

```
TX1  33 793 instr/atom      FOF  13 666        TH0   7 837
TF1  29 859                 TF0  18 551        TH1   5 832
TX0  19 301
```

And it is not a rounding error on small problems:

```
runs where parsing is >= 90% of the whole run's instructions:    55  (54 then hit -i)
                       50-90%:                                  488
                       20-50%:                                4 019
```

**4 562 runs — 17% of the corpus — spend at least a fifth of their entire instruction
budget parsing**, and 55 spend essentially all of it. `CSR061+6.p` (8.4 M atoms) burns
**102 G of its 104.9 G budget** in `parsing` and never starts proving. Of that, only 2 G
is `parsing.term sharing`, so the cost is in the parser proper, not in term construction.

Not yet localised below the node — `Parse/TPTP.cpp` has no finer `TIME_TRACE` scopes.
Adding a few would be the natural next step before optimising anything here.

---

## 4. The instruction-limit reporting race — fixed, and verified fixed

In the 11131 sweep `Lib/Timer.cpp:limitReached()` ran on the *timer thread* and printed
the time trace while the main thread was still proving and mutating it. **2 450 logs**
(~1 in 5 instruction-limited runs) died with `Aborted by signal`, and the abort always
landed inside the trace output.

Fixed on `martin-tstat` by freezing the trace rather than stopping the thread:
`TimeTrace::_enabled` is atomic and `limitReached()` clears it (plus a 1 ms settle) before
reporting; `ScopedTimer` remembers whether it pushed, so a frozen trace is never written
to again even by already-open scopes; `printPrettyRec` orders a local `vector<Node*>`
instead of sorting the live child list; and the whole subsystem uses `std::vector` and the
system allocator, so the timer thread never enters the prover's unsynchronised pool.
`limitReached` also flushes `std::cout`, which `std::_Exit` does not.

Verified on this sweep:

| | 11131 | 11142 |
|---|---|---|
| `Aborted by signal` | 2 450 | **0** |
| logs rejected as mangled | 2 952 of 26 504 | **0** |
| clean rate, every dialect x termination bucket | TH0 53%, TH1 27% at `-i` | **100.0% everywhere** |
| flat vs tree counter drift under `-i` | 8% of rows, up to 1.7% | **0 of 431 645 rows** |

That last row is the sharpest test: the two dumps are taken at different moments, so any
mutation between them shows up as flat > tree. `./ingest.py --selftest` now asserts exact
agreement there and would catch a regression of the freeze.

The old sweep's clean-rate bias also mattered for *what could be concluded*: TH0 at 53%
and TH1 at 27% meant no THF saturation claim was safe. That constraint is gone.

---

## 5. Peer outliers, and which of them are *not to fix*

`./rpt_peers.py` (3 640 rows). After the LRS group, which dominates it.

The detector's job is to find runs that behave unlike their peers, and it does — but a
large share of what it finds is the *problem* being hard, not the prover being wrong. Two
of the loudest signals in this sweep are cases where complexity theory says the blow-up is
unavoidable. They are kept here deliberately, marked, so they are not investigated a
second time.

**Not to fix — the theory is against us:**

- **`LCL648+1.010.p`** — `SAT solver` is **96% of the run** (100 G instructions) in 1 228
  calls, **82 M instructions per call** against a corpus median of 3 M: a 27x per-call
  cost, and the largest SAT anomaly in the sweep. The header reads
  `Problem : In K, pigeonhole formulae, size 10`. **Pigeonhole formulae have no
  polynomial-size resolution refutation** (Haken 1985), and CDCL is resolution, so an
  exponential blow-up here is a theorem, not a defect. At 109 ps/instr the solver is
  compute-bound — genuinely working, not thrashing. Nothing to fix, and the same applies
  to the rest of the `LCL64x` pigeonhole series and to any other pigeonhole encoding.
- **`SYN986+1.005.p` / `.006`** — `resolution` at 84.9% against a peer median of 0.1%
  (z = 443). The **Orevkov formulae**, a deliberate non-elementary proof-length benchmark.
  Same reasoning: the blow-up is the intended content of the problem.

Both are useful as positive controls: a detector that *failed* to flag them would be
broken. The lesson generalises — before chasing a peer outlier, read the problem's TPTP
header. A benchmark designed to be hard is not a performance bug.

**Expected, though not theoretically forced:**

- The `SWV421-1.4xx/5xx` and `SWV422-1.4xx/5xx` family sits at ~70% `SAT solver`, but at
  **5 M instructions per call it is barely above the 3 M median** — the share comes from
  making 13-14 k calls, not from any call being pathological. These are bounded model
  checking of a mutex algorithm at k = 400-500; heavy SAT work is what the problem *is*.
  No anomaly. (My earlier draft grouped this family with `LCL648` as "SAT solver
  blow-ups". That was wrong: only the per-call figure distinguishes a pathology from a
  problem that simply asks for a lot of solving, and by that figure these are normal.)

**Worth actually looking at:**

- **`SWC512_1.p`** — `SAT solver` 52% of the run at **14 M instructions per call**, 4.7x
  the median, and at 366 ps/instr it is memory-bound rather than compute-bound, unlike
  `LCL648`. An Atelier-B industrial proof obligation with no header suggesting deliberate
  hardness. This is the one case here where AVATAR may be asking the solver something
  avoidable.
- The `ITP2xx_3` (TX0) and `ITP0xx_5` (TF0) variants are LRS-bound at 62-77% while their
  `^1`/`+1` siblings are not. `./rpt_peers.py --family ITP007` shows this side by side.
  This is §1, not a separate finding.

---

## 6. Time and instructions rank the nodes differently, corpus-wide

The old §6 argued this from one hand-run problem. The full corpus now says it, and the
effect is one-directional in a way that is worth internalising: **exactly one cluster of
nodes is over-ranked by time, and everything else is under-ranked to compensate.**

`./rpt_hotspots.py --metric membound`:

| node | %instr | %time | t/i | ps/instr |
|---|---:|---:|---:|---:|
| LRS limit maintenance | 6.57% | 19.44% | **2.96x** | 548 |
| binary resolution index maintenance | 0.14% | 0.30% | 2.12x | 392 |
| passive container maintenance | 0.34% | 0.71% | 2.08x | 385 |
| backward superposition index maintenance | 0.44% | 0.89% | 2.04x | 378 |
| SAT solver | 4.56% | 5.90% | 1.30x | 240 |
| *— cliff to the corpus average of 185 —* | | | | |
| resolution | 19.09% | 17.25% | 0.90x | 167 |
| forward simplification | 17.93% | 15.89% | 0.89x | 164 |
| superposition | 16.39% | 11.56% | 0.71x | 131 |
| perform superposition | 13.54% | 12.48% | 0.92x | 171 |
| immediate simplification | 4.51% | 2.69% | 0.60x | 110 |

Four structure-walking nodes plus the SAT solver stall on memory; the actual inference
machinery runs at or below the corpus average. `forward demodulation index maintenance`
(1.06x) is *not* in the cluster, so this is not "all index maintenance" — it is
specifically these three indices plus LRS.

**The counters are validated independently.** `[root]`'s instruction count comes from
`rdpmc` through the mmap'd perf page; the statistics block's `Instructions burned` comes
from `read()` on the perf fd. Over all 11 975 instruction-limited runs their ratio is
1.0000 at p10, p50 and p90 — agreement to within the 2^20 rounding of the printed figure.

**A practical benefit beyond ranking**: `self_ns` can go *negative* on a node whose
children's printed (rounded) totals exceed its own — `NUM789^4.p`'s `main loop` has
self_ns = -191 µs. Instruction counts are exact integers, so `self_instr` never does this.

### Caveat: `Instructions burned` is mebi, not mega

`Lib/Timer.cpp` defines `MEGA = 1 << 20`, so `elapsedMegaInstructions()` divides by 2^20
and `-i 100000` is 104.9 G instructions, not 100 G — every such figure is 4.86% larger
than its label. Self-consistent and harmless for ratios, but the label is wrong.
Correcting it would silently reinterpret every existing `-i` value, including those baked
into portfolio schedules, so it is a decision for Martin rather than a fix.

---

## 7. What the machine noise actually is

`./rpt_ips.py --spread`, run against both sweeps' databases. Pinning 64 workers to
distinct physical cores, instead of running 120 unpinned, raised throughput by **1.70x**
(median 3 126 -> 5 327 M instr/s) but barely moved the p90/p10 spread (2.58x -> 2.50x).

That is not a failure of the pinning; it is evidence that this metric was never a clean
noise measure. It compares *different problems*, so it mixes genuine problem-to-problem
memory-boundedness with machine load, and the first term does not go away. §6's ps/instr
column shows how large that first term is.

The honest noise figure comes from repeating **one** problem: `./determinism.py` gives a
median per-node instruction spread of 0.004-0.015% under `setarch -R`, against wall-time
spreads of 0.45-49.7% on the same runs. So instruction counts should be believed to ~0.1%
and time only to the tens of percent.

---

## 8. Not superlinear, which is worth stating

`./rpt_preproc.py --fit` was built to find a preprocessing step that is quadratic in input
size. Across every dialect and every pre-saturation node, the fitted exponent is 0.75-1.30
— **nothing is superlinear**. The one mild exception is `property evaluation` on TX0 (1.30
[1.28, 1.32]) and TH0 (1.27), which is §2 showing up as a slope rather than as outliers.

The old sweep's sublinear parsing exponents (b = 0.29-0.79) were the NFS floor, not a
scaling property; they are now 0.93-1.23. So the preprocessing problems in this corpus are
constant factors, not complexity bugs — which is why §2 and §3 are both phrased as cost per
atom.

---

## 9. What the LRS maintenance cap actually did (11156 vs 11142)

`vampire_z3_rel_martin-tstat_11156 -i 100000 -tstat on`, same corpus, same machine
setup, `-lrs_maintenance_budget` at its 0.05 default. Runs were **purely
instruction-limited**, so instructions are the binding resource and the cap applies to
them. 26 265 usable runs again, 0 crashes, selftest clean.

### The cap holds exactly

Per-run share of a run's own instructions spent in `LRS limit maintenance`, over the
18 946 runs where the node appears:

| | median | p90 | p99 | max | runs over 5% |
|---|---:|---:|---:|---:|---:|
| 11142 (uncapped) | 1.15% | 15.69% | 27.63% | **64.34%** | **36.1%** |
| 11156 (`-lmb 0.05`) | 0.16% | 2.06% | 3.10% | **4.76%** | **0.0%** |

No run exceeds the budget, and the maximum lands just under it. That is the mechanism
doing exactly what it says.

Corpus-wide the node falls from **6.57% of instructions to 0.95%** (87.9 T → 12.7 T) and
from **19.44% of time to 5.86%** (48 145 s → 12 766 s), on 152.9 M → 24.6 M updates.

Note the corpus figure (0.95%) sits far below the 5% cap. That is expected: the cap is a
ceiling applied per run, most runs were never near it, and the cumulative form also
thins the early updates — after each one it waits for saturation to catch up, and early
in a run there is little to catch up to.

### The freed budget becomes search, and it is measurable

On the 10 488 problems that hit the instruction limit in *both* sweeps — same budget
spent, so a clean throughput comparison — 11156 performs **3.34% more activations** on
average. Corpus-wide the 75.2 T instructions taken out of LRS reappear in the inference
machinery:

```
resolution                 +23.8 T      SAT solver           +5.4 T
forward simplification     +13.7 T      superposition        +4.9 T
perform superposition       +8.0 T      LRS limit maintenance  -75.2 T
```

### Under an instruction limit, 5% of instructions is not 5% of time

The time share only falls to 5.86% corpus-wide, with a p90 of 11.15% and a **max of
34.54%** per run. This is the memory-boundedness of §6 showing up as a design
consequence rather than an observation: capping the resource that ends the run
(instructions) leaves the wall-clock share three to seven times higher.

It gets worse after capping, not better — `LRS limit maintenance` goes from 548 to
**1004 ps/instr**, from 2.96x the corpus average to 6.15x. The updates that survive are
the late, expensive, cache-hostile ones, and with fewer of them each starts from a colder
cache. So the cap trades *many cheapish* updates for *few expensive* ones.

**This is the thing to decide before the PR.** If the goal is a 5% share of wall clock
rather than of instructions, the budget under `-i` has to be either applied to time
regardless of which limit binds, or set nearer 0.015 in instruction terms.

### The cost win is solid; the solved-problem win is not

| | 11142 | 11156 | delta |
|---|---:|---:|---:|
| Refutation | 12 820 | 12 857 | **+37** |
| Instruction limit | 11 975 | 11 948 | −27 |
| Satisfiable | 1 067 | 1 067 | 0 |
| Refutation not found, non-redundant clauses discarded | 105 | 95 | −10 |

Gained 60, lost 32, **net +28**, and **zero soundness contradictions** — no problem got
two different definite SZS statuses across the two sweeps.

But +28 out of ~13 900 solved is not a result to lean on. Martin's own paired experiment
at `-i 64K`, `-lmb 1.0` against `-lmb 0.05` on the same corpus, gives 12 666 → 12 678
(+12), with 18 problems solved only by `1.0` against 30 only by `0.05` — a spread
comparable to what re-running an LRS strategy produces by itself. **Treat the solved
count as unchanged.** What the change reliably buys is the 5.6 percentage points of
corpus instructions moved out of overhead and into inference, and the removal of the
64%-of-a-run worst case; whether that converts into problems is below the noise floor
of a single sweep.

The `non-redundant clauses discarded` drop (105 → 95) is a small independent sign the
limits are now less aggressive: that reason is reported exactly when LRS discarded
something it later needed.

> Toolkit bug found while doing this, now fixed: `RE_TERM` in `common.py` excluded the
> hyphen, so `Refutation not found, non-redundant clauses discarded` failed to match at
> all and 95 runs recorded an empty termination. That is precisely the category worth
> watching when changing LRS, and it had been invisible in every earlier analysis.

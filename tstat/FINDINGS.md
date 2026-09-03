# Findings from the master-11131 sweep

Each entry names the reproducer and the command that shows it. Read `README.md` first —
three of the four measurement hazards there change how these numbers should be read.

Corpus: 23 750 trustworthy runs, 355 798 s of exclusive time.

---

## 1. `LRS limit maintenance` is 25% of all time, and quadratic in run length

`./rpt_hotspots.py` — 88 638 s self time, **24.91% of the corpus**, 131.9 M calls,
672 µs/call, 0% instrumentation. Also 13.5% of the mean per-run share, so it is
pervasive, not a few pathological runs. `./rpt_percall.py --node-summary` puts the
recoverable time at 50 154 s, twice the next node.

**Mechanism.** `LRS::poppedFromUnprocessed` (`Saturation/LRS.cpp:41`) calls
`_passive->updateLimits()`, which (`Saturation/ClauseContainer.cpp:60`) runs a *full
simulation*: `simulationInit()` then `simulationPopSelected()` repeated
`estReachableCnt` times. The early-out only fires when `estReachableCnt >
sizeEstimate()`, i.e. while passive is still small.

Measured cost per call against the run's final passive size:

```
passive ~  1 834   median   22 us/call
passive ~ 16 496   median  222 us/call
passive ~ 44 463   median  679 us/call
passive ~117 785   median 3065 us/call      log-log slope 1.01, r = 0.82
```

Linear in passive size. And `LRS::shouldUpdateLimits()` (`Saturation/LRS.cpp:57`) fires
on a **fixed counter** — every 500 activations, or every **50** once limits are active —
with no regard for what an update costs. Total cost is therefore
`O(activations/50 x |passive|)`, i.e. quadratic in run length: the longer the run, the
worse the fraction. That is why it is so visible at `-i 100000`.

**Minimally-intrusive fix**: make the cadence adaptive in `shouldUpdateLimits()` — keep
the measured cost of limit maintenance under a fixed fraction of elapsed time (or scale
the interval with `sizeEstimate()`), instead of the constants 500/50. Purely a policy
change; no data structure touched.

Worst individual runs (`./rpt_percall.py`): `BIO004+1.p` (17 ms/call, 104 s),
`HWV088-1.p` (13 ms/call), `SYN906-1.p`, `SYN912-1.p`, `HWV098-1.p`, and the whole
`ITP2xx_1/_3` group. `./rpt_peers.py` flags the same set independently: `BIO004+1.p`
spends 86.7% of its main loop here against a peer median of 35.7%.

**Caveat**: this node walks a large structure, so the 120-way parallel sweep's memory
contention inflates its *share* somewhat. The mechanism and the linear-in-passive
scaling are contention-independent; the exact 25% is not.

---

## 2. `Property::scan` is very expensive on HOL, and runs several times per problem

`./rpt_preproc.py --outliers` — the top non-parsing rows are a whole TH0 family:

```
NUM796^4.p  property evaluation  size 12.0k  15.0s  predicted 31ms  488x over
NUM792^4.p  property evaluation  size 11.2k  13.0s  predicted 28ms  459x
NUM789^4.p ... NUM795^4.p        same shape, 12-15 s each
NUN053^4.p  preprocessing        size 26.3k  11.5s  209x
```

**Reproduces locally on disk** (so it is not the NFS artifact):
`./rerun.sh NUM789^4.p -t 40` gives `property evaluation (total: 4360 ms, avg: 1090 ms,
cnt: 4)` on a problem that *parses* in 7.4 ms. One scan costs 150x a full parse, and it
happens four times.

**Mechanism** (`sample` on the preprocessing phase, 5 s of samples):

```
3710  Shell::Property::scan(UnitList*)   <- via Problem::getProperty() -> refreshProperty()
3307    Shell::Property::scan(Clause*)
1082      Shell::Property::scan(TermList, bool, bool)
 473        Kernel::SortHelper::getArgSort
 387        Kernel::SortHelper::getTypeSub
 365        Kernel::SortHelper::getResultSort
 176        Kernel::SubtermIterator::hasNext
```

75% of the phase is inside one `Property::scan`. `Property::scan(Literal*)`
(`Shell/Property.cpp:605`) does

```cpp
for (int i=0; i<arity; i++) { scanSort(SortHelper::getArgSort(lit, i)); }
```

and every `getArgSort` call rebuilds the entire type substitution from scratch
(`SortHelper::getTypeSub`, `Kernel/SortHelper.cpp:68`, binds all type arguments into a
fresh `Substitution`) before applying it to one argument. Scanning a term of arity n
costs n substitution builds instead of one. In HOL every `@` is polymorphic, so this is
the whole traversal — NUM789^4.p has 6 002 `@` connectives.

**Two independent fixes, both small:**

- a bulk `SortHelper::getArgSorts(const Term*, Stack<TermList>&)` that calls
  `getTypeSub` once and applies it to each `ot->arg(i)`. `Shell/Property.cpp:605` and
  `:715` are the hot callers; the same `for i < arity: getArgSort(t,i)` pattern appears
  in ~10 further places (`Shell/BlockedClauseElimination.cpp:477`,
  `Inferences/TheoryInstAndSimp.cpp:134,209`, `Indexing/AcyclicityIndex.cpp:71,84`,
  `Inferences/TermAlgebraReasoning.cpp:384,397`, ...), so one helper fixes all of them.
- find out why `Problem::refreshProperty()` runs 4 times here. Per `CLAUDE.md`, the
  `Problem` property cache is invalidated by transformations and silently repaired by
  the next `getProperty()`; at ~1 s a scan on HOL, each spurious invalidation is a
  second of wall time.

Corpus-wide `property evaluation` is 1 550 s (0.44%) with 59 657 calls over 23 698 runs
— 2-3 scans per run everywhere, and `./rpt_preproc.py --fit` puts TH0 at 2 281 ns per
input atom against 703 for FOF.

---

## 3. `parsing` in this sweep measures NFS, not the parser

Not a prover finding, but it invalidates the most obvious reading of the data, so it is
worth stating plainly. `parsing` is 32.5% of the mean per-run share — the single largest
entry by that measure — and it is an artifact:

| | server (sweep) | local disk |
|---|---|---|
| `SET044+1.p` | 113 ms | 220 µs |
| `SYN952+1.p` (size 5) | 71 ms | 244 µs |
| `SYO837+1.p` | 174 ms | 271 µs |
| `NUM789^4.p` | — | 7.4 ms |

Every FOF problem pays a ~21 ms floor regardless of size, +1.5 ms per `include()`
(median 21.0 ms at 0 includes, 28.0 ms at 6). The TPTP release was on `/nfs/...` with
120 jobs reading it. `rpt_percall.py` excludes `parsing` by default; the sublinear
exponent it gets in `rpt_preproc.py --fit` (b = 0.29-0.79) is this constant, not a
scaling property.

To get a real parsing measurement, the sweep needs TPTP on local disk.

---

## 4. The instruction-limit reporting path is racy — diagnosed and fixed

`Lib/Timer.cpp:limitReached()` runs on the **timer thread**: it writes
`env.statistics->print(std::cout)` — which reaches `TimeTrace::printPretty`
(`Shell/Statistics.cpp:339`) — and then `System::terminateImmediately(1)`, all while the
main thread is still proving and still mutating the trace.

- **2 450 logs** contain `Aborted by signal` (2 120 SIGSEGV, 27 SIGBUS, plus SIGABRT and
  mangled variants) — **about one in five of the ~12–13 k instruction-limited runs**.
- 2 239 more logs have a missing or duplicated profile section.
- The crash is precisely located: in **all 2 450** logs the abort line lands *inside* the
  time-trace output — 1 676 inside the flattened profile, 774 inside the trace tree,
  **zero before it**.
- The race is visible even in the survivors: the trace tree and the flattened profile
  agree *exactly* on all 467 111 rows from normally-terminated runs, and differ on 8% of
  instruction-limited rows, always flat > tree (counters still growing between the two
  dumps), by up to 1.7%.

> Counting trap: `grep -l 'Aborted by signal' *.log` gives 1 900, because grep skips
> files it judges binary and the interleaved logs contain invalid UTF-8. Use `grep -la`.

**Three memory-unsafe interactions**, all in the reporting path:

1. `printPrettyRec` sorted `children` **in place** — a `Lib::Stack<unique_ptr<Node>>`
   that the main thread's `ScopedTimer` constructor scans and appends to. A concurrent
   append reallocates the array the sort is writing into.
2. `printPretty` iterates `_stack` twice while every `TIME_TRACE` scope pushes and pops
   it, ~10⁹ times per run.
3. `Node` carried `USE_ALLOCATOR(Node)` and `Lib::Stack::expand` uses `ALLOC_KNOWN`, both
   routing to `GLOBAL_SMALL_OBJECT_ALLOCATOR` — plain free lists, **no synchronisation**
   (`Lib/Allocator.hpp:246`). `Node::flatten()` allocated dozens of nodes on the timer
   thread while the main thread allocated clauses from the same lists. This one corrupts
   silently and faults later, which is why it only showed up under load.

**Fixed on `martin-tstat`** by freezing the trace rather than stopping the thread:
`TimeTrace::_enabled` is now atomic and `limitReached()` clears it (plus a 1 ms settle)
before reporting; `ScopedTimer` remembers whether it pushed, so a frozen trace is never
written to again, not even by already-open scopes; `printPrettyRec` orders a local
`vector<Node*>`; and the whole TimeTrace subsystem uses `std::vector` and the system
allocator so the timer thread never enters the prover's pool. `limitReached` also
flushes `std::cout`, which `std::_Exit` does not.

---

## 5. Peer outliers worth a look (and one instructive false positive)

`./rpt_peers.py` (3 273 rows). After the LRS group:

- **`SYN986+1.005.p` / `.006`**: `resolution` at 81-83% of the main loop against a peer
  median of **1.4%** (z = 40), 55 s excess. Reproduces locally: 312 resolution calls at
  22 ms each, 5.2 M `term sharing` calls, 2.4 GB peak — on a problem with 3 formulae.
  This is the **Orevkov formula**, a deliberate non-elementary proof-length benchmark;
  the blow-up is the problem, not the prover. Useful to know the detector finds these,
  and that they should be excluded rather than chased.
- **`SWC512_1.p`**: `SAT solver` at 59.6% against a peer median of 1.8% (z = 72), 33 s.
  Not obviously inherent — worth a look at AVATAR on TX0.
- The `ITP2xx` / `ITP0xx` families split by dialect: the `_1`/`_3` (TF0/TX0) variants are
  LRS-bound at 60-76% while their `^1`/`+1` siblings are not. `./rpt_peers.py --family
  ITP007` shows this side by side.

## 6. First instrumented run: time and instructions rank the nodes differently

`AGT001+1.p`, `-tstat on -t 10 -p off`, on the server, with the new per-node
instruction counters. Depth-1 nodes as a share of `[root]`:

| node | % of time | % of instructions | G instr/s |
|---|---:|---:|---:|
| parsing | 23.8% | 55.0% | 4.09 |
| main loop | 3.9% | 15.3% | 6.83 |
| preprocessing | 2.3% | 13.2% | 10.33 |
| property evaluation | 2.0% | 14.3% | 12.81 |
| **`[root]` self (untraced)** | **68.1%** | **2.2%** | **0.06** |

**The counters are validated.** `[root]` reports 60 M instructions; the statistics
block's `Instructions burned` reports 57, and those two reach the same hardware event
by completely independent paths (rdpmc through the mmap'd page vs `read()` on the fd).
They agree to 0.4%, the residual being the statistics block printed between the two
reads. See the caveat below on what "57" means.

**Two thirds of a short run's wall clock is not executing user code.** `[root]`'s own
time — everything outside any `TIME_TRACE` node — is 68% of the run but 2% of the
instructions, running at 0.06 G instr/s against 4-13 G/s everywhere else. That is
process start-up, dynamic linking, page faults and I/O. It also means the "`parsing` is
32.5% of the mean per-run share" headline in `rpt_hotspots.py` was measuring the
environment as much as the parser.

**Time badly under-ranks `property evaluation`.** 2.0% of the time but **14.3% of the
instructions** — a 7x difference — because the time denominator is inflated by all that
non-executing wall clock. This corroborates finding 2 far more strongly than time did:
three `Property::scan`s cost a seventh of the CPU work of a *first-order* run, before
saturation has done anything.

The general lesson for the next sweep: rank by instructions, and use time only via
`ps_per_instr` to spot the memory-bound nodes.

### Caveat: `Instructions burned` is mebi, not mega

`Lib/Timer.cpp` defines `MEGA = 1 << 20`, so `elapsedMegaInstructions()` divides by
2^20. The printed `Instructions burned: 57 (million)` is therefore 57 x 2^20 =
59 768 832, and `-i 100000` is 104.9 G instructions rather than 100 G — every such
figure is 4.86% larger than its label claims. This is what makes the cross-check above
work: against a true 57 x 10^6 the gap would be 5.3%, far too large to be explained by
printing a few lines.

Harmless in itself (it is self-consistent, and ratios are unaffected), but the label is
wrong. Correcting the arithmetic would silently reinterpret every existing `-i` value,
including those baked into portfolio schedules, so that is a decision rather than a fix.

## 7. Machine noise floor, for interpreting anything above

`./rpt_ips.py --spread` over 11 723 runs of at least 5 G instructions:

```
p10  1 828 M instr/s     p50  3 126     p90  4 724       p90/p10 = 2.58x
```

A run at p10 takes 1.71x longer than the median for identical work. Part of that is
genuine memory-boundedness — median throughput falls monotonically with peak memory,
4 530 M instr/s under 64 MB down to 2 672 at 256 MB-1 GB — and part is contention
between the 120 parallel jobs. Ratios *within* one run are sound; absolute per-call
comparisons *between* runs carry this factor.

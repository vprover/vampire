# tstat — mining a `-tstat on` sweep for optimization targets

Analysis toolkit for the DVTIME_PROFILING sweep in
`../problemsALLlocal_tstat11142_tstat-on_i100K/` (26 504 TPTP problems,
`vampire_z3_rel_martin-tstat_11142 -i 100000 -tstat on`, TPTP on local disk, 64 workers
pinned one per physical core, ASLR off). **26 265 runs are usable**; the 239 that are not
are Vampire user errors that never reached profiling.

Nothing here touches the prover. Everything reads logs and writes CSVs into `out/`.

Cost is measured in **retired instructions** by default, with wall time kept alongside.
Every report takes `--metric time` for the old view. The reason is in `FINDINGS.md` §6:
time over-ranks the memory-bound nodes by up to 3x, and instruction counts are
reproducible run to run where time is not.

## Setup

Scripts need numpy; the interpreter with it is **`/opt/local/bin/python3.14`**
(the `python3` first on `$PATH` is a conda 3.11 without numpy). The shebangs already
point at it.

```sh
./ingest.py              # ~25s, builds tstat.db
./ingest.py --selftest   # integrity checks; must print SELFTEST PASSED
```

## Reports

| script | question |
|---|---|
| `rpt_hotspots.py` | where the work goes, corpus-wide and per dialect (`--by-dialect`, `--tree`). `--metric membound` ranks by ps/instr: which nodes stall on memory |
| `rpt_preproc.py` | is any pre-saturation step superlinear in input size (`--fit`), and which problems cost far more than their size predicts (`--outliers`, `--percost`) |
| `rpt_percall.py` | which runs pay far more *per call* for a node than usual, ranked by recoverable cost (`--node-summary` for the per-node spread) |
| `rpt_peers.py` | which runs spend their saturation time unlike near-identical problems (`--family CSR115` dumps one family) |
| `rpt_ips.py` | instructions per second: `--spread` sizes the wall-clock spread across runs; default lists memory-bound runs |
| `determinism.py` | repeats one problem under `-al` and compares per-node instruction vs time spread — the honest noise floor |
| `calib_overhead.py` | what one `TIME_TRACE` scope costs, so we know which nodes measure themselves |
| `q.sh` | ad-hoc SQL: `./q.sh "SELECT node, SUM(self_instr) FROM vtree GROUP BY 1 ORDER BY 2 DESC LIMIT 10"` |
| `rerun.sh` | reproduce one problem locally and diff its profile against the sweep |

`rpt_hotspots.py`, `rpt_preproc.py` and `rpt_percall.py` all take
`--metric {instructions,time}` and default to instructions.

## Schema

`runs`, `tptp`, `stats`, `nodes_flat`, `nodes_tree`, plus the joined views `v`
(one row per run), `vflat` and `vtree` (profile rows, already restricted to
trustworthy runs). `nodes_tree.path` is the dotted ancestry, so parse-time
`term sharing` is distinguishable from the saturation-time one; `self_ns` and
`self_instr` are exclusive (total minus direct children), and `ps_per_instr` is their
ratio.

One reason to prefer `self_instr`: the printer rounds each node's total to 3-4
significant figures, so a parent whose children round up can end with a *negative*
`self_ns` (`NUM789^4.p`'s `main loop` is -191 µs). Instruction counts are printed as exact
integers, so `self_instr` never goes negative.

## Reading the data: two live hazards, and two that are now history

**1. Wall clock is not comparable between runs; instructions are.** `rpt_ips.py
--spread`: effective throughput runs from 3 444 M instr/s at p10 to 8 616 at p90, so a run
at p10 takes 1.55x longer than the median for exactly the same work.

Pinning 64 workers one per physical core instead of running 120 unpinned raised median
throughput 1.70x but left this spread almost unchanged (2.58x → 2.50x), which shows what
the number really is: it compares *different problems*, so it mixes machine load with
genuine problem-to-problem memory-boundedness, and the second term does not go away.
Median throughput still falls monotonically with peak memory — 8 486 M instr/s under
64 MB, 5 994 at 64–256 MB, 4 624 at 256 MB–1 GB.

The clean noise figure comes from repeating *one* problem (`determinism.py`, below):
0.004–0.015% per-node instruction spread against 0.45–49.7% in time. So compare
instructions between runs freely, and time only within a run.

**2. The profiler perturbs the fine-grained nodes — but the size of the effect is now
measurable.** `TIME_TRACE_ITER` (`Lib/Metaiterators.hpp:1011`) wraps every
`hasNext()`/`next()`, so `term sharing` records 21.6 G calls and `clause generation`
16.3 G. Instrumentation costs a *constant number of instructions* per scope, which the
sweep bounds directly: over nodes with more than 3×10⁸ calls the cheapest is `splitting`
at **107 instructions per call**, and it does real work, so a `ScopedTimer` costs no more
than that. Against `clause generation` at 657 instructions/call and `term sharing` at 723,
instrumentation is therefore under 16% — not the 43% the old time-based estimate claimed
from a 26 ns figure measured on a Mac laptop.

The `instr/call` column in `rpt_hotspots.py` is the thing to read; treat a node near 100
as measuring itself. Calibrating the constant exactly (so it can be *subtracted* rather
than flagged) needs `calib_overhead.py` re-run with instruction counting on the sweep
machine — worth doing, not yet done.

### Two hazards the 11142 sweep removed

Kept here because they are why the 11131 sweep's numbers must not be compared against
this one.

**Mangled logs — gone.** `Lib/Timer.cpp:limitReached()` used to print the time trace from
the *timer thread* while the main thread was still mutating it: 2 450 of 26 504 logs died
with `Aborted by signal`, about one in five instruction-limited runs. Fixed (`FINDINGS.md`
§4); this sweep has **0** crashes, **0** rejected logs, and a **100.0%** clean rate in
every dialect × termination bucket. The old sweep's rejects were badly non-uniform —
instruction-limited TH0 was 53% clean and TH1 27% — so no THF conclusion drawn from it is
safe.

> Counting trap, corrected: the old note here said to use `grep -la`. That is still wrong.
> `grep -l` reports 1 900 of those logs and `grep -la` reports 2 241; the true count is
> **2 450**. Interleaved output defeats both. Only a byte-level scan is reliable:
> `open(f,'rb').read()` and search for the bytes.

**`parsing` measuring NFS — gone.** The TPTP release used to live on `/nfs/...` with 120
jobs hammering it, giving every FOF problem a ~21 ms floor regardless of size. With TPTP
on local disk, `SET044+1.p` went from 113 ms to **212 µs** and `SYO837+1.p` from 174 ms to
266 µs — matching what the same problems cost from local disk on a laptop. The node's
sublinear exponent in `rpt_preproc.py --fit` (b = 0.29–0.79) was that fixed floor; it is
now 0.93–1.23, cleanly linear. `rpt_percall.py` no longer excludes `parsing`, and what the
node now shows is a real and previously invisible cost — see `FINDINGS.md` §3.

## Instruction counts (sweeps built after Sep 2026)

`TIME_TRACE` now records user-space instructions retired alongside wall time, so each
node line carries a further field:

```
[root] (total: 39 ms, avg: 39 ms, cnt: 1, instr: 118 M)
```

It reads `instr: -` when the hardware counter was unavailable (not Linux, no
`perf_event_open`, or no user-space `rdpmc`). The parser treats the field as optional,
so logs from older sweeps still ingest — they simply get `NULL` in the `instr`,
`self_instr` and `ps_per_instr` columns of `nodes_tree` / `nodes_flat`.

Two reasons this matters more than it might look:

- **Instruction counts are immune to hazard 1.** On the reference server a fixed
  workload measured 12 000 031 and 12 000 032 instructions across seven runs — a spread
  of 0.0000%, against the 2.5x spread in wall-clock throughput. Per-node instruction
  counts are therefore comparable between problems, between machines, and between
  builds, in a way ns never were.
- **Hazard 2 becomes correctable.** Instrumentation overhead is a *constant* number of
  instructions per scope, so it can be calibrated once and subtracted exactly
  (`true = measured − k·cnt`). Time can only ever be flagged, never corrected.

Keep reading time as well: `ps_per_instr` in the `vtree` view is picoseconds per
instruction per node, which is what separates "this node did more work" from "this node
is cache-missing" — the distinction hazard 1 otherwise destroys. `FINDINGS.md` §6 is that
distinction applied to the whole corpus.

### The measured noise floor

`determinism.py`, six problems x 3 runs, `-al 2000 -t 600 -sa otter` (otter rather than
LRS, whose limits depend on elapsed time and so make the search itself irreproducible),
on an otherwise quiet server:

| | median | worst node |
|---|---:|---:|
| instruction spread | 0.020% – 0.061% | 0.255% – 2.313% |
| time spread | 0.45% – 49.7% | 5.8% – 941% |

So **do not believe a per-node instruction difference below ~0.1%**, and treat anything
above ~1% as real. That is one to three orders of magnitude better than wall clock, and
it is measured on an *idle* machine — under a parallel sweep the time figures degrade by
the further 2.5x of hazard 1, while the instruction figures do not move at all.

### Run sweeps with ASLR off

That residual is genuine program variation, and most of it is **address-dependent**.
Repeating the same six problems under `setarch $(uname -m) -R`:

| problem | ASLR on | ASLR off |
|---|---:|---:|
| HWV114-1.p | 0.042% | 0.004% |
| PUZ016-1.p | 0.060% | 0.005% |
| SWW976_1.p | 0.039% | 0.015% |
| SWV767_5.p | 0.061% | 0.005% |
| PUZ098^5.p | 0.020% | 0.004% |
| BIO004+1.p | 0.030% | 0.010% |

An 8x tightening of the median for one flag, so **run comparison sweeps under
`setarch -R`**. `hvci retrieve`, the worst node on two problems, disappears from the
lists entirely, as does the bimodal `backward simplification` on `BIO004+1.p`
(22602031 / 22601755 / 22091101 — two runs agreeing to 0.001% and one 2.3% away, which
is a discrete difference in work, not jitter).

Note this is a *systematic* choice, not a cheat: with ASLR off every run shares one
address layout, so if that layout is cache-unfriendly all runs pay it equally. Fine for
A/B comparison, which is what sweeps are for.

**What the mechanism is not.** `hvci`'s own container is
`DHMap<unsigned, ClauseList*, FnvHash, IdentityHash>`, keyed on a *computed* hash, and
`VariableIgnoringComparator` (`Indexing/ClauseVariantIndex.cpp:178`) is deliberately
address-independent — ground terms are ordered by `Term::getId()`, with the comment "now
get just some total deterministic order while ignoring variables". So `hvci` is not
itself the source.

**What it most likely is.** The statistics blocks are *identical* across runs, so the
same logical work happens; only its cost changes. That is the signature of a container
hashed on pointers: the bucket distribution differs per run, so lookups take a different
number of probes and arrive at the same answers. `DefaultHash` on a `Term*` or a
`TermList` does exactly this — see the nondeterminism note in `CLAUDE.md`, which also
gives the fix (`SharedTermHash` / `SharedTermListHash`, id-based). Finding the specific
container is a separate hunt; the instruction counters now make it tractable, since they
localise *which node's* cost moves.

An earlier draft of this file blamed shifted `Term::getId()` values. That was
speculation, and Martin's objection is right: ids are assigned in creation order, and
creation order changing per run would have caused visible trouble long before now. The
pointer-bucket explanation needs no such shift.

A residual of ~0.005% median survives ASLR being off. For a deterministic program that
should be zero, so there is something else too — worth knowing, not worth blocking on.

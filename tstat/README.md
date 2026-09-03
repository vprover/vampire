# tstat — mining a `-tstat on` sweep for optimization targets

Analysis toolkit for the DVTIME_PROFILING sweep in
`../problemsALL_master11131_tstat-on_i100K/` (26 504 TPTP problems,
`vampire_z3_rel_..._11131 -i 100000 -tstat on`, 120 jobs in parallel).

Nothing here touches the prover. Everything reads logs and writes CSVs into `out/`.

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
| `rpt_hotspots.py` | where does the time go, corpus-wide and per dialect (`--by-dialect`, `--tree`) |
| `rpt_preproc.py` | is any pre-saturation step superlinear in input size (`--fit`), and which problems cost far more than their size predicts (`--outliers`, `--percost`) |
| `rpt_percall.py` | which runs pay far more *per call* for a node than usual, ranked by recoverable time (`--node-summary` for the per-node spread) |
| `rpt_peers.py` | which runs spend their saturation time unlike near-identical problems (`--family CSR115` dumps one family) |
| `rpt_ips.py` | instructions per second: `--spread` measures how noisy the sweep's machine was; default lists memory-bound runs |
| `calib_overhead.py` | what one `TIME_TRACE` scope costs, so we know which nodes measure themselves |
| `q.sh` | ad-hoc SQL: `./q.sh "SELECT node, SUM(self_ns)/1e9 FROM vtree GROUP BY 1 ORDER BY 2 DESC LIMIT 10"` |
| `rerun.sh` | reproduce one problem locally and diff its profile against the sweep |

## Schema

`runs`, `tptp`, `stats`, `nodes_flat`, `nodes_tree`, plus the joined views `v`
(one row per run), `vflat` and `vtree` (profile rows, already restricted to
trustworthy runs). `nodes_tree.path` is the dotted ancestry, so parse-time
`term sharing` is distinguishable from the saturation-time one; `self_ns` is
exclusive time (total minus direct children).

## Reading the data: four hazards, all real

**1. Mangled logs (2 952 of 26 504 dropped).** `Lib/Timer.cpp:limitReached()` runs on
the *timer thread*: it prints `env.statistics` and calls `terminateImmediately` while
the main thread is still proving and mutating the time trace. **2 450 logs carry
`Aborted by signal`** (2 120 SIGSEGV) — about one in five instruction-limited runs — and
the abort always lands inside the trace output. See `FINDINGS.md` §4 for the diagnosis
and the fix. (Count these with `grep -la`: plain `grep -l` skips the interleaved logs as
binary and reports only 1 900.) `ingest.py`
rejects anything that fails a structural check, and the selftest confirms the cost:
the trace tree and the flattened profile agree **exactly** on all 467 111 rows from
normally-terminated runs, and disagree only under `Instruction limit` (8% of rows,
always flat > tree, ≤1.7%) — which is the same race, caught in the act.

The rejects are not uniform: instruction-limited **TH0 is 53% clean and TH1 27%**,
against 85% for CNF/FOF. Do not read a THF saturation conclusion off this sweep
without checking how many runs survived.

**2. `parsing` measures the server's NFS, not the parser.** Every FOF problem shows a
fixed ~21 ms floor no matter how small it is, +1.5 ms per `include()`. The same
problems parse in 220–520 µs locally from disk (`SET044+1.p`: 113 ms on the server,
220 µs here). The TPTP release was on `/nfs/...` and 120 jobs were hammering it. The
`parsing` node is therefore excluded by default from `rpt_percall.py`, and its
sublinear exponent in `rpt_preproc.py --fit` is this artifact, not a scaling property.

**3. 120-way parallelism moves wall clock by 2.6x.** `rpt_ips.py --spread`: effective
throughput ranges from 1 828 M instr/s at p10 to 4 724 at p90, so a run at p10 takes
1.7x longer than the median for exactly the same work. Part of that is genuine
memory-boundedness (median IPS falls monotonically from 4 530 under 64 MB to 2 672 at
256 MB–1 GB) and part is contention. Wall-clock *ratios within one run* are sound;
absolute per-call comparisons *between* runs carry this 1.7–2.4x noise floor.

**4. The profiler perturbs the fine-grained nodes.** `TIME_TRACE_ITER`
(`Lib/Metaiterators.hpp:1011`) wraps every `hasNext()`/`next()`, so `perform
superposition` records 22.7 G calls and `clause generation` 14.0 G. One scope costs
26 ns here (`calib_overhead.py`), which is 31% of `term sharing`'s reported 146 ns/call
and 32% of `clause generation`'s 142 ns. The `instr%` column in `rpt_hotspots.py`
flags this; treat anything above ~30% as unmeasured.

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

- **Instruction counts are immune to hazard 3.** On the reference server a fixed
  workload measured 12 000 031 and 12 000 032 instructions across seven runs — a spread
  of 0.0000%, against the 2.6x spread in wall-clock throughput. Per-node instruction
  counts are therefore comparable between problems, between machines, and between
  builds, in a way ns never were.
- **Hazard 4 becomes correctable.** Instrumentation overhead is a *constant* number of
  instructions per scope, so it can be calibrated once and subtracted exactly
  (`true = measured − k·cnt`). Time can only ever be flagged, never corrected.

Keep reading time as well: `ps_per_instr` in the `vtree` view is picoseconds per
instruction per node, which is what separates "this node did more work" from "this node
is cache-missing" — the distinction hazard 3 otherwise destroys.

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
the further 2.6x of hazard 3, while the instruction figures do not move at all.

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

**`hvci` is the symptom, not the cause.** Its container is
`DHMap<unsigned, ClauseList*, FnvHash, IdentityHash>` keyed on a *computed* hash, and
`VariableIgnoringComparator` (`Indexing/ClauseVariantIndex.cpp:178`) is deliberately
address-independent — it orders ground terms by `Term::getId()`, with the comment "now
get just some total deterministic order while ignoring variables". But `getId()` is
assigned in term *creation* order. So something upstream enumerating a pointer-hashed
container creates terms in a different order, the ids shift, the comparator's ordering
shifts, and `hvci` pays different collision costs. It is simply the node most sensitive
to it. Finding that upstream container is the pointer-hashing hunt CLAUDE.md describes,
and is separate work.

A residual of ~0.005% median survives ASLR being off. For a deterministic program that
should be zero, so there is something else too — worth knowing, not worth blocking on.

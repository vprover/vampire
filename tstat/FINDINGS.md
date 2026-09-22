# Findings from the `-tstat` sweeps

Where Vampire's instructions go, measured over the whole of TPTP, and what has been done
about it so far.

Read `README.md` first for how to read the numbers and how to reproduce any of them.

> **The reference sweep is 11295.**
> `vampire_z3_rel_..._11295 -i 100000 -tstat on` (commit `e07474dc1`), 26 504 TPTP
> problems, TPTP on local disk, 64 workers pinned one per physical core, ASLR off.
> **26 273 usable runs** — the only 231 rejections are Vampire user errors that never
> reached profiling — 1 329 T instructions of exclusive cost, **78 distinct node names**.
> `tstat/tstat.db` and `common.py`'s `LOGDIR` point at it. It is the first sweep with the
> phase breakdown of §1, §2 and §9 in place; §19 is what it cost and what else moved.
>
> §20 indexes the nine sweeps taken so far and says which of the older databases are
> still worth keeping and why.
>
> Every node added in this round is a *child* of an existing one and nothing was renamed
> — the rule, not an accident: the whitelist is derived by scanning the source tree, so a
> renamed node would make all seven earlier databases unreadable at a stroke.

**Cost is counted in retired instructions unless stated otherwise.** That is not
cosmetic: time and instructions rank the nodes differently by up to 6x, and §11 is about
exactly that.

**Structure.** Part I is the open work, ranked. Part II is how to read the numbers
without fooling yourself. Part III is the history: each change that has been made, what
the sweep before and after it said, and what it bought. Nothing in Part III is a pending
task.

---

# Part I — Open targets

The measure here is deliberately **not** corpus share alone. The biggest nodes by share
are the inference machinery, which is supposed to be big. What earns a place below is
either a large share *or* a node that dominates individual runs — because that is where
a bounded fix has somewhere to bite, and because an outlier problem exposes an
inefficiency that the average run hides.

Counts are runs where the node exceeds 30% (and 50%) of that run's own instructions,
over the 11295 sweep. `resolution` and `codetree forward subsumption` are now *self*
figures with their new children broken out beneath them:

```
node                                   %corpus   >30%   >50%
superposition                           17.57%   2878   1244
codetree forward subsumption (interp.)  14.95%   3658   1341   <- §1
perform superposition                   13.92%   2123    980
resolution (= index retrieval)          13.80%   2143    640
perform resolution                       8.00%    504      8
SAT solver                               5.10%    964    240   <- §8
forward demodulation                     2.85%    411     78   <- §7
beta eta simplification                  2.81%    353    234   <- §3
codetree matcher setup                   1.65%      2      0   <- §1
parsing                                  1.09%   3115    658   <- §2
codetree multi-literal matching          0.92%    172*     —   <- §1, the tail
interpreted evaluation                   0.83%     53     36   <- §4
codetree literal ordering                0.61%      —      —   <- §9
```

\* runs where it exceeds **20%** of the run; 68% of the node is in those 172.

**The single largest structural fact this sweep produced** is not in any one row:
`resolution` self is index retrieval and `superposition` self is retrieval plus subterm
enumeration, so **substitution-tree retrieval is around 30% of the corpus** — more than
either inference rule's own work. Both rules split the same way, 63/37 and 56/44 in
favour of retrieval (§1, §10).

Two nodes have left this table since it was last drawn against 11156, and both left
because they were fixed: `forward simplification` (19.01% of corpus, 5 646 runs over
30%) is now 0.62% and 0 runs, because the work inside it has a name (§15); and
`property evaluation` (0.81%, up to 89% of a single run) is now 0.13% (§17).

## 1. `codetree forward subsumption` — 18% of the corpus, and two different pathologies

The whole subtree is **17.8%** of corpus instructions, second only to superposition's,
and until the 11165 sweep none of it was visible at all (§15). At 166 ps/instr it is
compute-bound, so unlike §5 this is not a cache-behaviour problem: it is a lot of work.
It is concentrated as well as large — **3 658 runs give the interpreter alone more than
30% of their instructions**, and the per-call cost varies by four orders of magnitude,
from 33 000 at the median to 2.75 **billion** on `GRA071^2.p`.

**The 11295 sweep splits it, and the split is the finding.** Corpus-wide:

| node | self | % corpus | calls | instr/call | share of the subtree |
|---|---:|---:|---:|---:|---:|
| the interpreter (`codetree forward subsumption` self) | 198.7 T | 14.95% | 7.12 G | 27 891 | **83.3%** |
| `codetree matcher setup` | 21.9 T | 1.65% | 7.12 G | 3 072 | 9.2% |
| `codetree multi-literal matching` | 12.2 T | 0.92% | 1.00 G | 12 172 | 5.1% |
| `codetree matcher teardown` | 5.7 T | 0.43% | 7.12 G | 799 | 2.4% |

So *on average* it is the code-tree interpreter, as the local reading on `GRA124-1.p`
suggested, and there is no phase to peel off: `Matcher::execute` dispatches one `CodeOp`
at a time and is deliberately not entered, because a scope inside it would cost more than
the ops it timed.

**But the average is not where the four orders of magnitude live, and there the answer is
different.** Of the 1 843 runs where the subtree exceeds half the run, **99 are dominated
by multi-literal matching rather than by the interpreter** — and those are the extreme
ones:

| problem | multi-lit % of run | interp % | calls | instructions per multi-lit call |
|---|---:|---:|---:|---:|
| `ANA073^1.p` | 91.2% | 8.5% | 2 874 | **33 263 603** |
| `ANA085^1.p` | 90.7% | 8.9% | 3 022 | 31 491 625 |
| `QUA001^1.p` | 92.7% | 5.2% | 6 487 | 14 991 553 |
| `QUA009^1.p` | 90.5% | 5.7% | 7 837 | 12 114 344 |
| `SEU686^2.p` | 89.2% | 9.5% | 8 167 | 11 460 637 |
| `ITP218^1.p` | 87.1% | 8.2% | 8 669 | 10 543 703 |

**68% of the whole `codetree multi-literal matching` node sits in 172 runs**, and every
problem at the top of that list is TH0. `GRA071^2.p`, the worst per-call figure in the
corpus, turns out to be 74.7% multi-literal matching in **twelve calls** — 6.5 G
instructions each — while `GRA124-1.p` next to it is 90.6% interpreter. The single
heading "forward subsumption is expensive" was covering two unrelated problems.

**Which half is actionable.** `ClauseMatcher::matchGlobalVars` /
`existsCompatibleMatch` (`Indexing/ClauseCodeTree.cpp`) is a backtracking search over
combinations of per-literal matches with **no bound on the search**, so a candidate with
many matches per literal explodes combinatorially. Thirty-three million instructions to
decide one subsumption is that explosion, it is confined to 172 runs, and a cap or a
better ordering of the match vectors is a bounded change. The interpreter half is the
larger number but the harder problem: 83% of the subtree spread thinly over 25 000 runs,
with no pathology to aim at.

> An earlier draft concluded from `GRA124-1.p` alone that "~93% is the interpreter" and
> that there was nothing to peel off. Corpus-wide that is right (83%); as a statement
> about the tail it was wrong, and the tail is what §1 has always been about. One
> problem was not a sample.

## 2. `parsing` — a fifth of the corpus gives it a fifth of its budget

1.17% of corpus instructions, which sounds negligible, and a per-run distribution that
is anything but:

```
runs where parsing is >= 90% of the whole run's instructions:     63
                       50-90%:                                   951
                       20-50%:                                  4 282
```

**5 296 runs — 20% of the corpus — spend at least a fifth of their entire instruction
budget in the parser**, and **54 spend 99% or more of it, so saturation never starts and
they report no SZS status at all.** In a corpus where every run is budget-bound this is
pure loss: the parser is spending the prover's search budget.

Of the four nodes that dominate the most runs, parsing is the only one that is not
inference. It has also *risen* in this ranking — 2 426 runs over 30% on 11156 against
3 449 now — which is mostly mechanical, since everything around it got cheaper, but it
is the reason parsing now outranks `superposition` on concentration.

**Scaling is not the problem.** `./rpt_preproc.py --fit --node parsing` is cleanly
linear in input size in every dialect (FOF b = 1.03 [1.01, 1.04], CNF 1.00, TF0 1.01).
The constant is the issue, and it differs by 5x across dialects:

```
TX1  31 578 instr/unit      CNF  15 519        TH0   7 346
TF1  23 374                 TF0  14 029        TH1   5 847
TX0  22 046                 FOF   8 814
```

> **What `size` is, and what it is not.** Every "input size" in this file and every
> `--fit` in `rpt_preproc.py` is the database's `size` column: the TPTP header's
> **atoms + connectives + variables**. The reports label its unit "atom"; it is really
> that sum. It is **not** a byte count and it can diverge from one by more than an order
> of magnitude in *either* direction:
>
> | problem | `size` | file on disk | why |
> |---|---:|---:|---|
> | `SWX146_1.p` | 42 | 167 KB | 31 atoms, but term depth 77 over 4 887 arithmetic applications, which `size` does not count (§4) |
> | `CSR061+6.p` | 8 365 857 | 2.7 KB | an `include()` wrapper; the axiom file it pulls in is **477 MB** |
> | `HWV133-1.p` | 10 577 953 | 278 MB | CNF, so literals + variables; here the file really is large |
>
> `size` is a fine regressor for the fits above — the exponents are unaffected by a
> constant factor — but any sentence of the form "an N-byte problem" must come from
> `wc -c`, not from this column. One in §4 did not, and was wrong.

The extreme tail is two distinct populations, and only one is a parser problem:

**Large inputs — CSR (SUMO/Cyc) and HWV (hardware verification).** This is where the
absolute cost is. `HWV132/133/134-1.p` — 2.33 M clauses in a **278 MB** file — each burn
the entire 104.87 G budget in parsing; the `CSR*+6` family is at 99.1%, reading a 2.7 KB
wrapper around a **477 MB** axiom file (`Axioms/CSR002+5.ax`). Of `CSR061+6.p`'s 102 G,
only 2 G is `parsing.term sharing`, so the cost is in the parser proper and not in term
construction.

Those byte counts settle one question before the sweep does. `HWV133-1.p` spends **377
instructions per input byte** and `CSR061+6.p` **214**; a tokeniser costs 5–20. So the
parser is an order of magnitude too expensive for lexing to be the explanation, whatever
the split below turns out to say — which is also why not scoping the lexer costs nothing.

**Short runs — SYN.** `SYN812-1.p` at 48.4%, `SYN842-1.p` at 31.6% and neighbours are
only 130–250 K input units; the share is high because the *run* is short. They finish
Satisfiable almost immediately and parsing is most of what happened. That is arithmetic,
not a defect, and it is why the 20–50% bucket should not be read as 4 282 problems worth
fixing.

**Split, and the answer is that the cost is in none of the places a boundary exists.**
The parser is a flat state machine, so it has no phases in the sense preprocessing does
— every state handler runs per token and is far too hot to scope. What it does have is a
boundary recurring once per input unit, and that is where the five new nodes sit. On
11295, corpus-wide:

| node | where | self | % of `parsing` |
|---|---|---:|---:|
| `tptp formula unit` | `endFof` — closing a formula off and handing it over as a `Unit` | 0.76 T | 4.9% |
| `tptp closure check` | the `freeVariables(f)` walk rejecting an unquantified variable | 0.33 T | 2.1% |
| `tptp type declaration` | `endTff` | 0.03 T | 0.2% |
| `tptp clause conversion` | the `mustBeClause` block in `endFof` | 0.02 T | 0.1% |
| `tptp include` | opening the axiom file, building the selection set | 0.004 T | 0.03% |
| **residue** (`parsing` self) | lexer + state machine + term and formula construction | **14.46 T** | **92.7%** |

The five together cost **0.03% of the corpus** to measure, as predicted. They rule out
everything they name: per-unit finalisation is 5%, the closure check 2%, and `include` —
which reads a 477 MB axiom file on the `CSR*+6` family — is *thirty thousandths* of one
percent. On the parse-bound outliers themselves the shape is the same, not worse:
`HWV133-1.p` spends 91.4% of its whole budget in `parsing` of which only 5.8% is
`tptp formula unit` and 1.9% clause conversion; `CSR061+6.p` 91.1%, of which 5.8% and
2.3%.

So **93% of parsing is the residue**, and the §2 note above already rules out the lexer
arithmetically — 214–377 instructions per input byte against 5–20 for a tokeniser. By
elimination the cost is the state machine and term/formula construction: `getTok` and
the `_states` loop, the per-token `std::string` in `Token::content`, symbol-table lookup
by name, and `Term`/`Formula` allocation. None of those has a per-unit boundary, which
is why this round could not localise it further.

**What would.** The next scope has to be per *token* or per *term*, which the §11 budget
forbids at 46 M tokens on `HWV133-1.p` — unless it is taken on a handful of problems
only, outside a sweep. That is the honest next step here: a one-problem `perf record` on
`HWV133-1.p`, not another sweep node.

## 3. `beta eta simplification` — a single call can eat a whole higher-order run

2.81% of corpus from only **4 806 runs**, of which **353 are above 30% of their own run
and 234 above 50%** — the highest >50%/>30% ratio of any node in the table, i.e. when it
bites it takes the run rather than a slice of it.

| problem | share of run | calls |
|---|---:|---:|
| `SYN007^4.014.p` | **100.0%** | **1** |
| `NUN109^1.p` | 99.4% | — |
| `NUN103^1.p` | 99.3% | — |
| `LCL931^1.p` | 98.7% | 33 |
| `NUM643^4.p` | 97.5% | 10 |

`SYN007^4.014.p` spends its entire 104.9 G budget inside **one** call to
`BetaEtaSimplify`. A single beta-eta normalisation that never returns is a bug, not a
tuning matter. 449 runs give the node more than 20% of their budget, and those 449 hold
28.2 T — **75% of the whole node**; the families are NUM (131), ITP (130), SYO (45) and
NUN (41), and the dialect is TH0/TH1 without exception.

`BoolSimp` is the same story one order down: 0.46% of corpus from 4 565 runs, 7 above
30%, worst 68.2%. It got 2.8x cheaper per call in the 11279 sweep as a side effect of
the `SortHelper` work (§17), which is evidence that the HOL simplification rules are
paying for sort computation rather than for simplification.

Neither rule could even be named before the 11165 sweep; `Inferences/HOL/` had no
instrumentation at all (§15).

## 4. `interpreted evaluation` — 4.7 M instructions per call on deep arithmetic

0.83% of corpus over 1 773 runs, 53 above 30% and 36 above 50%, and the tail is
remarkable for how *uniform* it is:

| problem | share of run | calls | instructions per call | max term depth | file |
|---|---:|---:|---:|---:|---:|
| `SWX146_1.p` … `SWX151_1.p` | **97.07%** | 21 825–21 827 | **4 664 5xx** | 77 | 167 KB |
| `SWX134/135/137/139_1.p` | 95.64% | 10 760–10 761 | 9 322 xxx | 40 | 333 KB |

Six problems agreeing to within 0.01% on all three figures is one root cause, not six,
and **4.66 M instructions to evaluate one clause** is the number worth chasing. 121 runs
give the node over 20% of their budget and those hold 52% of it; they are TF0 arithmetic
almost exclusively (118 of 121), families SWW (41), SWX (31), ANA (15), SWC (12),
ARI (12).

What makes them expensive is term *depth*, not input size. `SWX146_1.p`'s header reads
31 atoms and 9 connectives but `Maximal term depth : 77` and
`Number arithmetic : 7270 (26 atm; 4887 fun; 2355 num)` — thirty-odd atoms holding
almost five thousand arithmetic applications over two and a half thousand numerals. The
corpus median term depth is **4** and the 99th percentile is **38**, so these sit past
the far end of that distribution. Whether 4.66 M instructions is then a defect or simply
what normalising an expression that size costs is the open question; the six-way
agreement says that whatever it is, it is structural.

> **Correction.** An earlier draft of this section called these "42-byte problems" and
> made the small-input/large-cost contrast its headline. That was wrong, and the mistake
> is worth recording because the trap is still there: `size` in the database is the TPTP
> header's **atoms + connectives + variables**, not a byte count, and for these problems
> it is 42 while the files are 167 KB. It is blind to exactly what makes them hard —
> arithmetic term structure is counted on the header's `Number arithmetic` line, which
> `size` does not read. See the note under §2 on how far `size` can diverge from the
> input in *either* direction.

## 5. `LRS limit maintenance` — solved as a work problem, still the worst memory stall

The maintenance cap (§14) took this from the top of the file to 0.98% of corpus
instructions, and no run now gives it more than 5% of its own budget. As an
*instruction* target it is finished.

It is not finished as a *time* target, and the cap is why:

| sweep | %instr | %time | t/i | ps/instr |
|---|---:|---:|---:|---:|
| 11142 (uncapped) | 6.571 | 19.439 | 2.96x | 548 |
| 11156 (capped) | 0.953 | 5.857 | **6.15x** | 1004 |
| 11235 | 0.957 | 5.832 | 6.10x | 1008 |
| 11279 | 0.983 | 6.041 | **6.15x** | **1032** |

Against a corpus average of 168 ps/instr, what survives the cap runs at **6x the corpus
stall rate** and is still **6% of the prover's wall clock** for 1% of its work. The cap
traded many cheapish updates for few expensive ones: the updates that survive are the
late, large-passive, cache-hostile ones, and with fewer of them each starts from a colder
cache. The ratio has been stable across three sweeps, so this is structural, not noise.

**The open question, unchanged since §14 and worth deciding before anyone reopens this:**
if the goal is 5% of *wall clock* rather than 5% of instructions, the budget under `-i`
has to be either applied in the time unit regardless of which limit binds, or set nearer
0.015 in instruction terms. Under `-t 60` the cap already binds in the right unit and
buys ~10x more (§14).

## 6. The memory-bound index trio

With LRS capped, these are the only nodes left with a time/instruction skew above 2:

```
backward superposition index maintenance   0.42% instr   0.95% time   378 ps/instr
binary resolution index maintenance        0.16%         0.35%        363
passive container maintenance              0.39%         0.84%        363
```

About 1% of instructions but 2.1% of time, against a corpus rate of 168 ps/instr. A
small prize, and "make an index cache-friendlier" is not a cheap fix — but they are a
coherent group, and `forward demodulation index maintenance` (192 ps/instr) sitting
*outside* it says the cost is specific to these three rather than to index maintenance
generally. The skew is regime-independent: it holds at 2.1–2.5x under `-t 60` too (§13).

## 7. Demodulation — the folklore checked, and it is not quite right

The expectation was that demodulation eats a large share of long-lived runs. Share of a
run's own instructions in `forward demodulation`, bucketed by how long the run actually
was (11279):

| run length | n | median | p90 | p99 | max |
|---|---:|---:|---:|---:|---:|
| <1 G instr | 7 500 | 3.13% | 11.69% | 32.41% | 57.44% |
| 1–10 G | 1 484 | **8.45%** | **33.88%** | 56.98% | 68.10% |
| 10–50 G | 1 133 | 5.05% | 16.33% | 46.68% | 85.32% |
| 50–100 G | 346 | 2.01% | 9.42% | 53.09% | 70.11% |
| >100 G (budget-bound) | 10 406 | 2.12% | 6.08% | 26.70% | **88.55%** |

It peaks in the **middle** and falls away in the longest runs — the opposite of the
expectation, by a factor of four at the median. What is true is that the tail stays heavy
everywhere: 435 runs exceed 30% and the worst budget-bound run is at 88.6%. So
demodulation is worth looking at as a per-problem pathology rather than as a general tax
on long runs, and the runs to look at are the mid-length ones.

The node also got **15.7% cheaper per call** between 11235 and 11279, across every
dialect — see §17, which also explains why that number should not be read as a pure
speedup.

## 8. Peer outliers, and which of them are *not* to fix

`./rpt_peers.py` finds runs that behave unlike their peers, and it does — but a large
share of what it finds is the *problem* being hard, not the prover being wrong. These
are recorded so they are not investigated a second time.

**Not to fix — the theory is against us:**

- **`LCL648+1.010.p`** — `SAT solver` is 96% of the run (100 G instructions) in 1 228
  calls, 82 M instructions per call against a corpus median of 3 M: a 27x per-call cost,
  and the largest SAT anomaly in the sweep. The header reads
  `Problem : In K, pigeonhole formulae, size 10`. **Pigeonhole formulae have no
  polynomial-size resolution refutation** (Haken 1985), and CDCL is resolution, so an
  exponential blow-up here is a theorem, not a defect. At 109 ps/instr the solver is
  compute-bound — genuinely working, not thrashing. Same for the rest of the `LCL64x`
  series and any other pigeonhole encoding.
- **`SYN986+1.005.p` / `.006`** — `resolution` at 84.9% against a peer median of 0.1%
  (z = 443). The **Orevkov formulae**, a deliberate non-elementary proof-length
  benchmark. The blow-up is the intended content of the problem.

Both are useful as positive controls: a detector that *failed* to flag them would be
broken. The lesson generalises — read the problem's TPTP header before chasing a peer
outlier. A benchmark designed to be hard is not a performance bug.

**Expected, though not theoretically forced:**

- `SWV421-1.4xx/5xx` and `SWV422-1.4xx/5xx` sit at ~70% `SAT solver`, but at **5 M
  instructions per call they are barely above the 3 M median** — the share comes from
  making 13–14 k calls, not from any call being pathological. Bounded model checking of a
  mutex algorithm at k = 400–500; heavy SAT work is what the problem *is*. (An earlier
  draft grouped these with `LCL648`. That was wrong: only the per-call figure
  distinguishes a pathology from a problem that asks for a lot of solving.)

**Worth actually looking at:**

- **`SWC512_1.p`** — `SAT solver` 52% of the run at **14 M instructions per call**, 4.7x
  the median, and at 366 ps/instr memory-bound rather than compute-bound, unlike
  `LCL648`. An Atelier-B industrial proof obligation with no header suggesting deliberate
  hardness. The one case here where AVATAR may be asking the solver something avoidable.
- The `ITP2xx_3` (TX0) and `ITP0xx_5` (TF0) variants are LRS-bound at 62–77% while their
  `^1`/`+1` siblings are not. `./rpt_peers.py --family ITP007` shows this side by side.
  This is §5, not a separate finding.

## 9. Index maintenance, now that insert and remove are separate

`codetree subsumption index maintenance` (1.51% of corpus, 1.45 G calls) lumped two
operations that are nothing alike: insertion compiles a clause and merges the code into
the tree, removal runs the matching interpreter to find the clause's path and then
performs surgery. Each now has its own node, `codetree subsumption index insert` and
`codetree subsumption index remove`, **nested under the old one rather than replacing
it** — see the note below on why that is worth a scope.

Insertion is split further (three more scopes, on the insert half only):

| node | what it is |
|---|---|
| `codetree literal ordering` | `optimizeLiteralOrder`, the greedy heuristic choosing which literal to compile first. Quadratic in clause length — for each start position it walks every remaining literal's code against the tree — and it compiles all of them to do so, so the compilation below is the *second* time each literal is compiled |
| `codetree code compilation` | `LitCompiler` proper, plus `updateCodeTree` |
| `codetree code incorporation` | `incorporate`: matching the new code against an existing path, splitting a block, rebuilding search structures (`compressCheckOps`) |

Removal is left whole on purpose. Splitting its interpreter from its surgery would mean
a scope inside the per-`CodeOp` loop, which is the thing this instrumentation exists to
avoid; knowing what removal costs in total is the question that was actually open.

**Measured on 11295, and removal is not the story.** The whole subtree is 21.4 T, 1.61%
of corpus:

| node | self | % of corpus | calls | instr/call | share of the subtree |
|---|---:|---:|---:|---:|---:|
| `codetree literal ordering` | 8.12 T | 0.611% | 1 184 M | 6 860 | **38%** |
| `codetree code compilation` | 6.53 T | 0.491% | 1 184 M | 5 518 | 31% |
| `codetree code incorporation` | 3.58 T | 0.269% | 1 184 M | 3 022 | 17% |
| `codetree subsumption index remove` | 1.61 T | 0.121% | 245 M | 6 552 | **8%** |
| `codetree subsumption index insert` (own) | 1.10 T | 0.082% | 1 184 M | 926 | 5% |
| `codetree subsumption index maintenance` (own) | 0.41 T | 0.031% | 1 429 M | 286 | 2% |

So **insertion is 92% of index maintenance and removal 8%**, on a fifth as many calls —
removal is 7x more expensive per call than insertion's own bookkeeping, but there is so
little of it that the total is small. That answers the question the split was made to
answer: deletion is not where the money goes.

Where it goes is the *ordering heuristic*. `codetree literal ordering` alone is 8.12 T —
**five times the entire cost of removal**, and 0.61% of the corpus in its own right, more
than `splitting` or `boolean simplification`. It is `optimizeLiteralOrder`, which is
quadratic in clause length and compiles every literal a first time purely to run its
`evalSharing` walks, after which `codetree code compilation` compiles them all again.
That second compilation is another 6.53 T. Roughly **15 T, 1.1% of the corpus, is spent
deciding and then re-deciding how to lay a clause into the tree** — and it is a
self-contained, bounded piece of code with an obvious redundancy in it.

The local readings were right that the phases do not rank consistently (`GRA124-1.p`
59/26/10 against `CSR025+6.p` 18/9/65) but wrong about which dominates at scale: ordering
does, everywhere except the incorporation-heavy CSR shape.

**Why the parent node stays, at the cost of a scope.** Splitting a node by *renaming* it
is free — a call takes exactly one branch — and it was how this was first written. It is
still the wrong trade. The whitelist in `common.py` is derived by scanning the source
tree for `TIME_TRACE` literals, which is what stopped it drifting (§15); the price is
that a name leaving the source makes every sweep containing it unreadable, since an
unrecognised node rejects the whole run. Keeping the parent costs one scope per call —
1.45 G calls, **~0.012% of corpus**, 0.2% of the worst single run — and buys a rule with
no bookkeeping behind it: *add children, never rename*. Six sweeps' worth of this number
then stay directly comparable, and `_RETIRED_NODES` stays empty.

It does not stay empty for free forever: a node genuinely **deleted** with the code that
emitted it still needs an entry, so the mechanism is kept. `forward subsumption` — dead
in every sweep since `-cts` became the default — is the obvious future candidate.

One thing to watch when reading a trend: this node's `self_instr` changes meaning across
the split, from a leaf's cost to a container's ~0. Compare `instr` (the total), not
`self_instr`, across sweeps. The same caveat applies to `parsing` and
`codetree forward subsumption` in this round, and to `forward simplification` in §15 —
it is the normal consequence of a container gaining children, and the reason the schema
keeps the two columns apart.

## 10. What is still unattributed, and what it would cost to attribute it

An earlier draft of this section claimed the blind spots were closed, and listed only the
*container* nodes to prove it. That was circular: it defined away the four biggest
figures in the profile by calling them leaves. A leaf is not a node that does one thing,
it is a node we have not divided — and `resolution`'s 24 000 instructions per call are at
least two things.

So, honestly, on 11295 — the largest **self** figures whatever the node's role, and what
one more scope inside each would cost as a share of that node:

| node | self | % corpus | self/total | instr/call | one scope |
|---|---:|---:|---:|---:|---:|
| `superposition` | 233.6 T | **17.57%** | 52.1% | 33 411 | 0.32% |
| `codetree forward subsumption` (interpreter) | 198.7 T | 14.95% | 83.3% | 27 891 | 0.38% |
| `perform superposition` | 185.0 T | **13.92%** | 95.4% | 6 510 | **1.64%** |
| `resolution` (retrieval) | 183.5 T | **13.80%** | 63.3% | 15 734 | 0.68% |
| `perform resolution` | 106.4 T | 8.00% | 99.5% | 2 694 | **3.97%** |
| `SAT solver` | 67.8 T | 5.10% | 100.0% | — | 0.00% |
| `forward demodulation` | 37.9 T | 2.85% | 99.1% | 13 383 | 0.80% |
| `beta eta simplification` | 37.4 T | 2.81% | 98.9% | 117 000 | 0.09% |

**The last column is the whole decision**: ~107 instructions over the node's cost per
call, i.e. how much of what you would measure is the measurement. Below ~0.5% a scope is
free in practice; `perform superposition` at 1.64% and `perform resolution` at **3.97%**
are past the point where another scope inside starts measuring itself. The cautionary
case already in the tree is `term sharing`, at 15.1%.

**What was divided this round, and what it showed.** Four splits, one principle: scope
the phases that are *not* the hot inner loop and let the loop fall out as the parent's
self time — `Matcher::execute` dispatches one `CodeOp` at a time, retrieval yields one
candidate at a time, `readToken` runs per token, so a scope in any of them would cost
more than the ops it timed.

- `codetree forward subsumption` → §1. Interpreter 83%, but the tail is multi-literal
  matching, which is the actionable half.
- codetree index maintenance → §9. Insert 92% / remove 8%, and the ordering heuristic
  alone is five times all of removal.
- `parsing` → §2. The named boundaries account for 7%; the rest has no boundary.
- `resolution` → `perform resolution`, one scope at the top of
  `BinaryResolution::generateClause`, mirroring the `superposition` /
  `perform superposition` pair. **Retrieval 63% / construction 37%**, against 56/44 for
  superposition — the two main generating rules now agree that most of their cost is
  looking clauses up, not inferring with them.

That last one is the biggest single structural result in the sweep. `resolution` self
(13.80%) plus `superposition` self (17.57%) is **31% of the corpus in substitution-tree
retrieval and subterm enumeration** — more than either rule's own inference work, and
more than any other node in the file. It also makes `Indexing/SubstitutionTree` the
largest thing in the prover that has never been instrumented at all.

**What is left, in the order it is worth doing:**

- **`Indexing/SubstitutionTree` retrieval, ~31% of the corpus, no instrumentation at
  all.** This is now the biggest unmeasured thing in the prover, and the sweep is what
  promoted it: `resolution` self *is* retrieval, and `superposition` self is retrieval
  plus subterm enumeration. Both rules' retrieval iterators are lazy, so the cost is
  spread over `hasNext()` calls rather than sitting in a scopeable block, which is why
  it has escaped so far. The cheap way in is still `superposition`'s *other* half —
  scope `EqHelper::getSubtermIterator` and get retrieval by subtraction — but its cost
  depends on candidates per subterm *c*: 2 × 28.4 G / *c* scopes, so 0.046% at *c* = 10
  and **0.46% at *c* = 1**, and *c* is unmeasured. Measure it before adding anything,
  and measure it on **budget-bound runs**, not on short local ones — see §19 for why
  that distinction cost a 7x error last time.
- **`perform superposition`, 13.9%, and `perform resolution`, 8.0%.** Colour and
  ordering checks, substitution application, clause construction. Both are now past the
  comfortable range — 1.64% and **3.97%** per scope — so any further split here pays a
  real fraction of what it measures. `perform resolution` at 2 694 instructions per call
  is close to the floor at which this technique stops working.
- **`forward demodulation`, 2.9% and 99.1% self.** Untouched, 0.80% per scope. §7 says
  its pathology is per-problem and mid-length-run, so the split wants a hypothesis first.
- **`SAT solver`, 5.1%.** Third-party (Minisat / CaDiCaL / Z3). Out of scope; §12 notes
  it is the largest node that costs more clock than instructions.
- **`run`, 2.5% self over 26 K calls.** The saturation loop's own bookkeeping, 1.25 G
  instructions per run. Scopes are free at this frequency, but the cost is diffuse rather
  than concentrated in one call, so there is nothing obvious to wrap.

**And what is *not* worth dividing, so it is not rediscovered:** per-engine scopes inside
`CompositeISE::simplify` — `immediate simplification` is now 1 125 instructions per call,
so one scope is 9.5% of the node, against the 1.8% it would have been when the original
plan first declined this.

The FMB nodes remain untested by any sweep: the corpus is entirely default saturation
mode, so the four `fmb *` nodes and `minisat eliminate var` /
`minisat bwd subsumption check` have never been exercised. That wants a targeted
`-sa fmb` run, not a sweep. See `NEXT.md`.

---

# Part II — How to read these numbers

## 11. Instructions, not time

An earlier draft argued this from one hand-run problem; the corpus says it, and the effect is
one-directional in a way worth internalising: **one cluster of nodes is over-ranked by
time, and everything else is under-ranked to compensate.** `./rpt_hotspots.py --metric
membound` on 11279:

| node | %instr | %time | t/i | ps/instr |
|---|---:|---:|---:|---:|
| LRS limit maintenance | 0.98% | 6.04% | **6.15x** | 1032 |
| backward superposition index maintenance | 0.42% | 0.95% | 2.25x | 378 |
| binary resolution index maintenance | 0.16% | 0.35% | 2.16x | 363 |
| passive container maintenance | 0.39% | 0.84% | 2.16x | 363 |
| SAT solver | 5.18% | 6.80% | 1.31x | 220 |
| *— cliff to the corpus average of 168 —* | | | | |
| resolution | 21.54% | 20.81% | 0.97x | 162 |
| codetree forward subsumption | 17.79% | 17.54% | 0.99x | 166 |
| superposition | 17.73% | 13.59% | 0.77x | 129 |
| perform superposition | 14.07% | 14.32% | 1.02x | 171 |
| beta eta simplification | 2.81% | 1.52% | 0.54x | 91 |

Three structure-walking indices plus LRS and the SAT solver stall on memory; the
inference machinery runs at or below the corpus average. `forward demodulation index
maintenance` (1.15x) is *not* in the cluster, so this is not "all index maintenance".

**The counters are validated independently.** `[root]`'s instruction count comes from
`rdpmc` through the mmap'd perf page; the statistics block's `Instructions burned` comes
from `read()` on the perf fd. Their ratio over every instruction-limited run is 1.048 58
at p05 and p50, identical to five decimals across the 11165, 11233, 11235 and 11279
sweeps — and that constant is 2²⁰/10⁶, the quirk below, not an error in either reading.

**A practical benefit beyond ranking**: `self_ns` can go *negative* on a node whose
children's printed (rounded) totals exceed its own — `NUM789^4.p`'s `main loop` had
self_ns = −191 µs. Instruction counts are exact integers, so `self_instr` never does.

### Caveat: `Instructions burned` is mebi, not mega

`Lib/Timer.cpp` defines `MEGA = 1 << 20`, so `elapsedMegaInstructions()` divides by 2²⁰
and `-i 100000` is 104.9 G instructions, not 100 G — every such figure is 4.86% larger
than its label. Self-consistent and harmless for ratios, but the label is wrong.
Correcting it would silently reinterpret every existing `-i` value, including those baked
into portfolio schedules, so it is a decision for Martin rather than a fix.

## 12. The noise floor

`./rpt_ips.py --spread`: pinning 64 workers to distinct physical cores, instead of
running 120 unpinned, raised throughput by **1.70x** (median 3 126 → 5 327 M instr/s) but
barely moved the p90/p10 spread (2.58x → 2.50x). That is not a failure of the pinning; it
is evidence that this metric was never a clean noise measure. It compares *different
problems*, so it mixes genuine problem-to-problem memory-boundedness with machine load,
and the first term does not go away.

The honest figure comes from repeating **one** problem. `./determinism.py` gives a median
per-node instruction spread of **0.004–0.015%** under `setarch -R`, against wall-time
spreads of 0.45–49.7% on the same runs. So instruction counts should be believed to
~0.1% and time only to the tens of percent.

Under `-t 60` the floor is much higher — see §13.

## 13. Nothing is superlinear, and the two regimes measure different things

`./rpt_preproc.py --fit` was built to find a preprocessing step quadratic in input size.
Across every dialect and every pre-saturation node the fitted exponent is 0.75–1.30 —
**nothing is superlinear.** The one mild exception used to be `property evaluation` on
TX0 (1.30) and TH0 (1.27), which was §17's finding showing up as a slope rather than as
outliers; that step is now 13x cheaper. So the preprocessing problems in this corpus are
constant factors, not complexity bugs, which is why §2 is phrased as cost per atom.

**The two regimes are not comparable and should not be compared directly.** A
budget-bound run is 60 s / 355 G instructions under `-t 60` against 17 s / 105 G under
`-i 100K`, so the time-limited sweep gives every run 3.4x more work. Shares of fixed
costs move accordingly — in the 11156 pair, `parsing` reads 1.23% of the corpus under
`-i` and 0.45% under `-t`, and that is arithmetic, not a change in parsing.

- **`-i` measures search.** Work done is fixed by construction, so two builds are
  compared at identical effort and the only nondeterminism is the residual ~0.005%. It is
  the right tool for anything that changes *which* inferences happen, and it is what
  every reference sweep uses.
- **`-t` measures cost.** It is the only regime in which memory-boundedness is
  chargeable: under `-i`, a cache miss is free. Its per-problem noise floor is ~5%
  (measured, §14), so it settles no per-problem question on its own — but a corpus-level
  effect is comfortably outside it. Consult it when the question is about wall clock:
  the §11 skew, the §6 index trio, `SAT solver`.

Under `-t`, with LRS capped, **`SAT solver` is the largest node that costs more clock
than it costs instructions** — 5.96% of wall time against 3.74% of instructions, at 245
ps/instr. An instruction-limited sweep under-ranks it by a third, every time.

---

# Part III — Closed: what was measured, and what it bought

Each subsection is a change that has landed, the before-and-after sweep pair that
measured it, and the conclusion. None of it is pending work.

## 14. The LRS maintenance cap (11142 → 11156, and the t60s pair)

**The finding.** On 11142, `LRS limit maintenance` was **6.57% of corpus instructions
and 19.44% of corpus wall clock** — a t/i of 2.96x, the largest of any node, at 548
ps/instr against a corpus average of 185. It was not executing much code; it was walking
a large structure and missing cache.

`LRS::poppedFromUnprocessed` (`Saturation/LRS.cpp:41`) calls `_passive->updateLimits()`,
which (`Saturation/ClauseContainer.cpp:60`) runs a *full simulation*. The cadence in
`shouldUpdateLimits()` — 500, or **50** once limits are active — reads like "every 500 /
every 50 activations", but the counter advances once per clause *popped from
unprocessed*, and a single activation pushes many clauses through. Measured: **1.4
activations per limit update at the median, 0.2 at p10** — so in the median run a full
passive-set simulation runs more often than once per activation, roughly 36x more often
than reading the constant would suggest. Cost per update scaled with passive size
(23 k instructions at ~2 200 clauses, 784 k at ~106 000), roughly linear to 10⁵ then
flattening because `estReachableCnt` bounds the simulation.

**The change.** `-lrs_maintenance_budget`, default 0.05: keep measured limit maintenance
under a fixed fraction of the run. Later baked in as a constant (`d3f57446a`).

**What it did, under `-i 100000`** (11156, same corpus and machine):

| per-run share of own instructions | median | p90 | p99 | max | runs over 5% |
|---|---:|---:|---:|---:|---:|
| 11142 (uncapped) | 1.15% | 15.69% | 27.63% | **64.34%** | **36.1%** |
| 11156 (`-lmb 0.05`) | 0.16% | 2.06% | 3.10% | **4.76%** | **0.0%** |

No run exceeds the budget and the maximum lands just under it. Corpus-wide the node fell
from **6.57% to 0.95% of instructions** (87.9 T → 12.7 T) on 152.9 M → 24.6 M updates.
The 75.2 T reappeared in the inference machinery (`resolution` +23.8 T,
`forward simplification` +13.7 T, `perform superposition` +8.0 T), and on the 10 488
problems budget-bound in both sweeps — equal effort, so a clean throughput comparison —
11156 performs **3.34% more activations**.

**The solved-problem win under `-i` is not real.** Gained 60, lost 32, net **+28** out of
~13 900, zero soundness contradictions. Martin's own paired experiment at `-i 64K` gives
+12, with 18 problems solved only by `-lmb 1.0` against 30 only by `0.05` — a spread
comparable to re-running an LRS strategy by itself. Treat the solved count as unchanged.

**Under `-t 60` the payoff is ~10x, and the solved win *is* real.** This is the regime
this section was always about: the finding above stated the cost in wall clock, and only
`-t` applies the budget in that unit.

| per-run share of own wall time | median | p90 | p99 | max | runs over 5% |
|---|---:|---:|---:|---:|---:|
| 11142 (uncapped) | 3.37% | 33.33% | 48.33% | **80.00%** | **46.8%** |
| 11156 (`-lmb 0.05`) | 0.82% | 4.71% | 5.12% | 5.45% | 2.1% |

Corpus-wide **15.71% → 2.75% of wall time**, 31.77 h → 5.50 h, 26.27 hours moved out of
overhead and into inference (`resolution` +8.60 h, `forward simplification` +3.80 h,
`perform superposition` +2.54 h, `SAT solver` +2.48 h). Corpus totals **4 263 T →
4 639 T instructions (+8.8%) in 1.1% less wall time**; median machine throughput on runs
that used the full 60 s in both rises from **5.26 to 5.91 G instr/s** — same hardware,
more useful work per second, because the throttled node is the most memory-bound one in
the prover. Solved: gained 172, lost 43, **net +129**, zero soundness contradictions.

The gains sit where the throttle bound, which is what makes them believable:

| maintenance share in 11142 | lost | gained |
|---|---:|---:|
| node absent | 2 | 16 |
| <2% (control) | 8 | 9 |
| 2–10% | 2 | 7 |
| 10–30% | 17 | 59 |
| >30% | 14 | 81 |

**140 of the 172 gains (81%) come from the two hot buckets**, while the control bucket —
where the throttle provably cannot have bound — is 8 lost against 9 gained, exactly
balanced. The control group also measures the `-t` noise floor directly, over 2 511
time-limited runs where the change is a provable no-op: instructions p5 0.967, median
0.998, p95 1.049; within ±5% for five runs in six. **So a per-problem difference under
`-t` needs to clear ~5% before it means anything.**

`Refutation not found, non-redundant clauses discarded` fell in both regimes (105 → 95
under `-i`, 107 → 102 under `-t`) — a small independent sign the limits are now less
aggressive rather than more.

**What remains open** is §5: the cap bought the instruction share, and left behind a node
that is 6x more memory-bound than it was.

> Toolkit bug found here, now fixed: `RE_TERM` in `common.py` excluded the hyphen, so
> `Refutation not found, non-redundant clauses discarded` never matched and 95 runs
> recorded an empty termination — precisely the category worth watching when changing
> LRS, invisible in every earlier analysis.

## 15. The instrumentation (11156 → 11165)

Four commits closing the blind spots the 11156 analysis kept running into.
`vampire_z3_rel_martin-tstat_11165`, same corpus and setup, 1 080 535 flat nodes against
11156's 902 771.

**The blind spots closed, as predicted.** Unattributed *self* instructions per container:

| container | 11156 self | 11165 self |
|---|---:|---:|
| `forward simplification` | 253.5 T (**19.01%** of corpus) | 8.1 T (**0.61%**) |
| `immediate simplification` | 61.4 T (4.61%) | 13.2 T (0.99%) |
| `preprocessing` | 4.0 T (0.30%) | 0.5 T (0.04%) |
| `run` | 32.2 T (2.41%) | 32.1 T (2.41%) — untouched, as intended |

and it went where the diagnosis said: `codetree forward subsumption` 242.1 T,
`beta eta simplification` 32.4 T, `boolean simplification` 14.1 T, `eager clausification`
2.4 T, `preprocess 3` 1.6 T, `function definition elimination` 1.2 T, `FOOL elimination`
0.6 T. The old `forward subsumption` node appears in **0 of 26 265 runs**, confirming
that `-cts on` is what the corpus actually exercises.

**The instrumentation is free.** On the 11 508 runs budget-bound in both sweeps,
activations are a median 0.9996 of 11156's (mean 1.0002, p10 0.980, p90 1.017) — the
added scopes cost **0.04%** of the work done, against the 0.2% predicted from the
per-scope arithmetic. Solved counts move +4 / −1, zero soundness contradictions.

**What it revealed** is now §1 (forward subsumption was the second-largest node in the
prover and entirely invisible) and §3 (the HOL black box was `BetaEtaSimplify`). Both
displaced the shortlist that existed before them.

> Toolkit fix this sweep forced. `KNOWN_NODES` in `common.py` was a hand-kept list, and
> an unrecognised name rejects the *whole run* — so the 18 new node names caused
> **26 211 of 26 504 runs to be thrown away** on first ingest. It is now derived by
> scanning the source tree for `TIME_TRACE` literals and `TimeTrace::` constants
> (~0.4 s, 158 names), which cannot drift; and the rejection reason names the offending
> node, so the next such surprise is a one-line diagnosis rather than a hunt.

## 16. The rebase onto master, and a HOL defect it exposed (11233 → 11235)

11233 was taken to confirm three things after rebasing onto master `1254bdc09`, not to
discover anything. Two came back clean; the third found a defect in master.

**a. Instructions are read exactly as before.** The `rdpmc` inline `__asm__` was replaced
by `__builtin_ia32_rdpmc` when `Lib/PerfInstructions.hpp` was merged (`a606f3e9f`). The
ratio of the two independent readings of the same counter is 1.048 58 at median and p05
in both sweeps, identical to five decimals; instruction-limited runs stop in the same
place to 0.0004%.

**b. The profile is unchanged where it should be.** 63 node names in each, none unique to
either; corpus cost 1 136.63 T against 1 134.86 T over the 22 957 runs clean in both;
every top node within ±2% except `forward demodulation` at −5.3%.

**c. Master aborted on essentially all higher-order input.** **3 316 runs produced a
53-byte log reading `Not implemented at Kernel/FormulaTransformer.cpp:113` and nothing
else.** TH0 refutations fell 1 951 → 824, TH1 290 → 82.

`Shell/DistinctGroupExpansion.cpp`'s `DistinctExpander::applyLiteral` descends into a
literal's arguments to find `$distinct` hidden inside FOOL terms, guarded by
`if(!lit->shared())` as a proxy for "holds a special term". In higher-order logic a
literal containing a lambda is *also* unshared, so HOL terms enter the descent, reach
`FormulaTransformer::apply(TermList)` and hit `case SpecialFunctor::LAMBDA:
NOT_IMPLEMENTED`. Two changes in PR #936 combine: `c7032a41b` removed the
`hasDistinctGroups()` guard from `Shell/Preprocess.cpp` (correctly — a `$distinct` marker
can exist with no group yet), so the pass now runs on every problem; `3d8a07043` added
the FOOL descent. Four lines reproduce it, with no `$distinct` anywhere:

```tptp
thf(p_decl, type, p: ($i > $o) > $o).
thf(q_decl, type, q: $i > $o).
thf(ax, axiom, (p @ (^[X: $i]: (q @ X)))).
thf(co, conjecture, (?[F: $i > $o]: (p @ F))).
```

Verified against a clean build of `1254bdc09`, not merely against our branch, so the
attribution is not an inference. **Fixed** by "Do not run DistinctGroupExpansion on
higher-order problems": the pass is skipped for higher-order input, and a higher-order
problem that does carry a distinct group — a distinct object still parses in thf, in an
equality and in a type declaration — is rejected rather than silently losing the
disequalities it asserted.

`checks/sanity` could not have caught this: its one end-to-end higher-order entry,
`hol/hol1.p`, has a higher-order *variable* but no lambda, and every other thf entry
stops at `--mode output`, before preprocessing runs. The same commit adds `hol/hol2.p`
(the reproducer) and `hol/hol-distinct-object.p` (the rejected case).

**d. 11235 confirmed the fix at corpus scale.** 26 273 clean runs against 11165's 26 265,
the only rejections the 231 pre-existing user errors; TH0 refutations 1 949, TH1 290 —
back to 11165 levels. 13 818 solved against 11165's 13 814, zero soundness
contradictions, the same 63 node names, the `rdpmc` cross-check unchanged. The new
`USER_ERROR` fires **0 times** in TPTP, as predicted.

`distinct group expansion` became an **always-on** preprocessing step in the process:
21 393 of 26 273 runs against 247 in 11165. Cheap — 47.48 G instructions, 0.0036% of
corpus, worst single run 0.678% of itself — but a new entry on every first-order path.
The 4 880 runs without it are exactly the higher-order ones, which is the skip being
visible in the profile. Two benign residues: 54 non-HOL runs lack it because they burned
the whole budget in parsing and never reached preprocessing (the `CSR*+6` / `HWV13x-1`
family of §2); and 13 `^`-named problems do have it, being first-order in practice.

## 17. The cheaper `Property::scan` (11235 → 11279)

`vampire_z3_rel_..._11279` (`248fb8b61`), same corpus and setup, master's "cheaper scan"
work in place: ~50 commits removing `Signature::Symbol::usageCnt`, walking the term DAG
rather than the tree it unfolds to, short-circuiting `GoalGuessing`, and rewriting how
`SortHelper` computes an application's sorts. 26 273 clean runs, the same 231 user
errors, selftest clean.

**The finding it answers.** On every sweep up to 11235, `property evaluation` was 0.81%
of corpus but consumed whole runs: the `NUM76x–NUM79x^4` family at 67–89% of a full
104.9 G budget, 2–4 scans each, all of them then hitting the instruction limit with
saturation nowhere. `Property::scan(Literal*)` called `SortHelper::getArgSort` once per
argument, and each call built a fresh `Substitution` binding *every* type argument before
applying it to the one argument asked for — so scanning a term of arity n cost n
substitution builds instead of one. In HOL every `@` is polymorphic, so that was the
whole traversal.

**The win, corpus-wide.** The scan's own node falls 84%, and the symbol counting it used
to do on the side reappears as a new `symbol counts` node (`Kernel/SymbolUsage.cpp`, one
call per run, at the `PrecedenceOrdering` construction rather than inside preprocessing):

| | 11235 | 11279 |
|---|---:|---:|
| `property evaluation` | 10.74 T (0.806%) | 1.72 T (0.130%) |
| `symbol counts` | — | 0.58 T (0.044%) |
| **together** | **10.74 T (0.806%)** | **2.30 T (0.173%)** — **−78.6%** |

**The win on the outliers, honestly stated.** The scan itself is ~2 000x cheaper on the
NUM family, but the work did not vanish — it moved into the single cheap counting pass,
which on exactly these problems is the expensive part. Counting both nodes:

| problem | 11235 | 11279 | factor |
|---|---:|---:|---:|
| `NUM795^4.p` | 88.90% of run | 7.20% | **12.4x** |
| `NUM796^4.p` | 88.78% | 7.29% | 12.2x |
| `NUM793^4.p` | 73.97% | 5.98% | 12.4x |
| `NUM789^4.p` | 67.18% | 5.43% | 12.4x |

A 12x reduction on the worst family in the corpus, uniform across it. `symbol counts` is
now their largest pre-saturation cost at ~7% of the run, which is a real but much smaller
target than what it replaced.

**The larger win was somewhere else, and was not the stated goal.** Two of the commits
landed in `Kernel/SortHelper.cpp` — `463490415` "Read an application's sorts off the term
instead of substituting" and `52b51a1ab` "Instantiate declared sorts by indexing the
term, not through a map" — and `getResultSort` has callers far beyond `Property::scan`.
Three nodes got systematically cheaper **per call**, in 86–99.8% of runs, across every
dialect:

| node | calls | instructions/call | per-run median ratio |
|---|---:|---:|---:|
| `boolean simplification` | +14.6% | 63 800 → 24 127 (**−62.2%**) | 0.355 |
| `term sharing` | +3.2% | 682 → 466 (**−31.7%**) | 0.668 |
| `forward demodulation` | +4.2% | 15 993 → 13 484 (**−15.7%**) | 0.771 |

That is 7.9 T + 4.8 T + 5.3 T = **18 T recovered, twice what the scan itself gave back**.
`boolean simplification` calls `SortHelper::getResultSort` on every non-variable subterm
of every literal, so it was paying the §17 cost per subterm and now is not; that it is
also the node most helped is the cleanest confirmation of the mechanism.

**A caveat on `forward demodulation`, and on the churn.** `8d47d9b9f` ("Build the
ordering's frequencies from the clauses, not from the signature") changes *what* the
default `sp=frequency` precedence is on any problem whose cached `Property` had gone
stale — its own message calls this out as sweep-worthy. So 11235 → 11279 is **not** a
pure same-search-cheaper-code comparison for the ordering-dependent nodes, and part of
`forward demodulation`'s −15.7% is a different search rather than faster code. The sweep
is the answer to whether that was a good trade, and it is:

**No regression anywhere.** 105 problems gained, 47 lost, **net +58** (13 928 → 13 986),
**zero soundness contradictions**, no node name lost. The gains are led by **CSR (29)**,
the SUMO/Cyc family with the largest signatures in TPTP — which is where a cheaper
signature scan should show up, and a mechanistic confirmation rather than a coincidence.
By dialect: FOF 53, CNF 21, TH0 12, TF0 7, TH1 7. Losses are unconcentrated (NUM 6, SET 6,
ITP 3, then twos).

**Where the freed budget went.** Under `-i`, a saving does not reduce the corpus total —
it buys more saturation. Corpus self-instructions fall only 0.41% (1 332.8 T → 1 327.3 T,
and that is the newly-solved problems finishing early), while the inference nodes rise at
**flat per-call cost**, which is exactly the signature of "same code, run more":

```
superposition            +8.68 T  (+3.8%, instr/call +0.4%)
resolution               +5.47 T  (+2.0%, instr/call −0.1%)
beta eta simplification  +4.77 T  (+14.6%, instr/call +0.1%)
SAT solver               +2.12 T  (+3.2%)
```

**Nothing else changed.** One new node name (`symbol counts`); no node disappeared. The
rebase checks of §16a hold: the `rdpmc` cross-check is unmoved.

**Not detectable here: LRS.** Master gained the maintenance cap through this branch, so
from master's point of view the LRS estimate is new — but both 11235 and 11279 already
contain it (`6e275ba98` … `d3f57446a` are ancestors of both), and no commit between the
two sweeps touches `Saturation/LRS.cpp`. §14 remains the measurement of that change; §5
records that its share has been stable at 0.95–0.98% across all three sweeps since.

## 18. The instruction-limit reporting race — fixed, and verified fixed

In the 11131 sweep `Lib/Timer.cpp:limitReached()` ran on the *timer thread* and printed
the time trace while the main thread was still proving and mutating it. **2 450 logs**
(~1 in 5 instruction-limited runs) died with `Aborted by signal`, and the abort always
landed inside the trace output.

Fixed on `martin-tstat` by freezing the trace rather than stopping the thread:
`TimeTrace::_enabled` is atomic and `limitReached()` clears it (plus a 1 ms settle)
before reporting; `ScopedTimer` remembers whether it pushed, so a frozen trace is never
written to again even by already-open scopes; `printPrettyRec` orders a local
`vector<Node*>` instead of sorting the live child list; and the whole subsystem uses
`std::vector` and the system allocator, so the timer thread never enters the prover's
unsynchronised pool. `limitReached` also flushes `std::cout`, which `std::_Exit` does not.

| | 11131 | 11142 onwards |
|---|---|---|
| `Aborted by signal` | 2 450 | **0** |
| logs rejected as mangled | 2 952 of 26 504 | **0** |
| clean rate, every dialect x termination bucket | TH0 53%, TH1 27% at `-i` | **100.0% everywhere** |
| flat vs tree counter drift under `-i` | 8% of rows, up to 1.7% | **0 of 431 645 rows** |

That last row is the sharpest test: the two dumps are taken at different moments, so any
mutation between them shows up as flat > tree. `./ingest.py --selftest` asserts exact
agreement there and would catch a regression of the freeze.

The old clean-rate bias also mattered for *what could be concluded*: TH0 at 53% and TH1
at 27% meant no THF saturation claim was safe. That constraint is gone, which is what
makes §3 possible.

One more artifact retired in the same move: in 11131, `parsing` measured the server's NFS
mount rather than the parser, and the whole node was written off. With TPTP on local disk
the artifact is gone (`SET044+1.p`: 113 ms then, **212 µs** now) and what is left is real
— §2. The old sublinear parsing exponents (b = 0.29–0.79) were the NFS floor, not a
scaling property.

## 19. The 11295 sweep: what the phase breakdown cost, and what else moved

`vampire_z3_rel_..._11295` (`e07474dc1`), the first sweep with §1's, §2's, §9's and
§10's twelve new nodes. 26 273 clean runs, the same 231 user errors, selftest clean,
1 384 836 flat nodes against 11279's 1 107 726.

**It is not a pure instrumentation comparison, and that has to be said first.** Master
advanced between the two binaries: six `FlexibleTail` commits (a safe-flexible-array
abstraction threaded through `Clause`, `SATClause` and `SkipList::Node`, plus a
pointer-downcast hazard fix) and the two commits separating `Map`/`Set` equality from
their hash parameter. So a per-problem difference here can be either change, and the
sections below separate them where it matters.

### The instrumentation costs 0.2%, as predicted

Equal-effort comparison over the 11 494 runs budget-bound in **both** sweeps, the same
test §15 used:

```
activations 11295/11279:  p10 0.9572   median 0.9978   mean 0.9908   p90 1.0071
```

**Median −0.22% of the work done**, against ~0.25% predicted. Scope-count arithmetic
says 58.7 G net new scopes × ~107 instructions = 6.3 T = 0.47% of corpus, so the
measured cost is about half the arithmetic — consistent with 107 being an upper bound on
the per-scope cost rather than a typical value.

Solved: 13 986 → 13 960, **net −26** (18 gained, 44 lost), **zero soundness
contradictions**. That is the honest price of the breakdown, and it is the largest an
instrumentation round has cost so far (§15's was +3).

### The tail is search perturbation, not slowdown

The mean (−0.92%) is much worse than the median because of a tail, and it is worth
saying what that tail is not. Distribution of the activation ratio:

| ratio | runs | |
|---|---:|---|
| <0.80 | 62 | 0.5% |
| 0.80–0.95 | 847 | 7.4% |
| 0.95–1.05 | 10 188 | **88.6%** |
| 1.05–1.25 | 364 | 3.2% |
| >1.25 | 33 | 0.3% |

**Roughly symmetric** — 62 runs lose more than 20%, 33 gain more than 25% — which is the
signature of a reordered search, not a slower prover. Confirmed directly: on
`SWX094_1.p`, the worst-hit run (activations ×0.24), the new scopes account for **0.02%
of the run** by count, while `interpreted evaluation` went from 13 533 to 296 306
instructions per call — a different clause population, not a slower one. Per `CLAUDE.md`,
individual problems flipping under a change like `FlexibleTail` is expected and is not
itself a defect; the 0 soundness contradictions are the check that matters.

### `FlexibleTail for SkipList::Node` is visible, and is a wash

Per-call cost ratios 11295/11279 for nodes with **no** new scope inside them are 1.000
at the median almost everywhere — `superposition` 1.000, `perform superposition` 0.998,
`forward demodulation` 0.997, `beta eta simplification` 1.000, `splitting` 1.000. Two
are not:

| node | instr/call | ps/instr | wall |
|---|---|---|---|
| `passive container maintenance` | 2 885 → 3 186 (**+10.4%**) | 363 → 325 (−10.5%) | 1 881 s → 1 840 s |
| `hvci compute hash` | −2.1% | — | — |

The passive container is `SkipList`, so the +10.4% is `FlexibleTail for SkipList::Node`
and the interquartile range is 1.102–1.117 — a tight, systematic change, not noise. But
the node got *less* memory-bound by almost exactly the same factor, so it retires 8.9%
more instructions in 2% **less** wall time. A layout change that trades instructions for
locality, and on this hardware the trade is slightly favourable. Worth recording because
under `-i` it reads as a 0.03%-of-corpus regression while under `-t` it would read as a
small win — §13's point about the two regimes, arriving unprompted.

### The methodological lesson: measure ratios on budget-bound runs

The `perform resolution` cost estimate was **7x too low**, and the reason generalises.
Its frequency was measured locally as 0.48 calls per `resolution` scope entry, on four
problems under `-al`. Corpus-wide under `-i 100000` it is **3.4** (39.48 G against
11.66 G), so the real cost is 0.32% of corpus, not 0.046%.

The cause is `.filter(NonzeroFn())` in `generateClauses`: `generateClause` returns 0 when
the LRS age/weight limits reject the clause *before* building it, so one `hasNext()`
consumes as many candidates as it takes to find one that survives. On a short local run
LRS limits are not yet active and nearly every candidate survives; on a budget-bound
sweep most do not. **A call-frequency ratio measured where LRS is not binding does not
transfer to a sweep**, and the same trap is waiting for the `superposition` enumeration
measurement §10 asks for.

## 20. Sweep index

Nine sweeps exist. All are `-tstat on` over the same 26 504 TPTP problems, same machine,
64 workers pinned one per physical core, ASLR off.

| sweep | limit | database | what it is for |
|---|---|---|---|
| master-11131 | `-i 100000` | — | superseded; NFS-mounted TPTP, and the trace race of §18 |
| 11142 | `-i 100000` | `tstat-11142.db` | the before-picture for §14 (uncapped LRS) |
| 11156 | `-i 100000` | `tstat-11156.db` | LRS capped; the before-picture for §15 |
| 11165 | `-i 100000` | `tstat-11165.db` | first instrumented sweep; the before-picture for §16 |
| 11233 | `-i 100000` | `tstat-11233.db` | **superseded, do not use** — the §16c HOL defect loses 3 316 runs. Kept only as that section's evidence |
| 11235 | `-i 100000` | `tstat-11235.db` | the before-picture for §17 |
| 11279 | `-i 100000` | `tstat-11279.db` | the before-picture for §19 |
| **11295** | **`-i 100000`** | **`tstat.db`** | **the standing reference** — first with the phase breakdown (§19) |
| 11142/11156 pair | `-t 60` | `tstat-t60s-*.db` | the only regime where memory-boundedness is chargeable; §13, §14 |

Future `-i` sweeps stay on `-i 100000` so they remain comparable to this chain. Keep the
`-t 60` pair for wall-clock questions and re-measure there rather than converting (§13).

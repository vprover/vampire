# Generated tests and independent expectations

Run a suite with `run.py run --build BUILD --suite NAME --output NEW_DIRECTORY`.
Use the repository-relative commands in [README.md](README.md) for a working
quick start. Inputs, oracle descriptions and validator results are saved with
each run. A fixed seed makes generated choices reproducible.

- Propositional clause sets and Boolean expressions use complete truth tables.
- Small quantified relations/functions use explicit finite witnesses or
  reductions that establish the expected formula's truth or contradiction.
- Parser cases distinguish malformed-input rejection from valid syntax that
  the implementation does not support. Assertions do not satisfy rejection
  contracts.
- Arithmetic uses exact Python integers and fractions for signed division,
  remainders, rounding, conversions and selected array identities. SAT/UNSAT
  controls accompany the identities. Backend traces distinguish translation
  from simplification before the backend runs.
- Datatype graphs use finite constructor trees for acyclic SAT witnesses and
  strict-height cycle contradictions for UNSAT expectations.
- Propositional interpolation checks both implication conditions and the
  shared-atom restriction. This validator accepts its generated fragment.
- Finite-model certificates require complete interpretation tables and check
  the generated constraints independently. This is a bounded single-sort
  checker, not a general TPTP model validator.
- Portfolio and induction cases test selected dispatch contracts. Dispatch
  does not prove every strategy in a schedule ran.

Transformation round trips invoke Vampire again and can miss shared errors.
Emitted proof obligations are checked with Z3, with unsupported steps retained
as inconclusive. Passing obligations do not certify missing introduction steps
or arbitrary complete proofs. These weaker guarantees remain labelled.

## Native reference checks

SharedSet compares against `std::set`; IntUnionFind uses graph reachability;
StringUtils uses an independent edit-distance calculation. Congruence-closure
tests check finite equivalence/congruence relations and core subsets, while
ground models are checked by a structural rewriter. Schedule and unification
tests exercise their stated API contracts. All 65 added functions are included,
including the ten failing regressions documented in the
[README](README.md#added-c-tests). The previous qualification recorded 55
added passes and ten failures, alongside 1,981 original passes. The failures
remain enabled in CTest and retain their normal failure status. These counts
do not establish general API correctness or a new coverage measurement.

## Measure and extend coverage

Use a matching GCC/gcov toolchain and wait for all instrumented processes to
exit before capture. `coverage.py` combines zero-hit and executed captures so
unexecuted instrumented code remains in the denominator. The README describes
the source filters, output files and optional threshold.

The [overlay helper](coverage-overlay.md) writes new counters into a fresh
tree while preserving a frozen baseline. It hashes inputs, verifies exact
object-local sums and rejects changed identities or invalid counters. Use
the source path embedded in the original build, even if the harness is in
another checkout. Failed or interrupted captures remain evidence.

`reachable_coverage.py` is an optional proof-ledger validator. It retains raw
coverage and accepts only individually reviewed, build-specific mappings;
unsupported, exception, assertion and bug-blocked paths are not automatically
excluded. Read its `--help` and the overlay instructions before use.

New native tests can change template instances and denominators. Measure each
binary separately. A test that aborts before GCC flushes counters can execute
a path without recording a hit; its raw gap remains visible. Never clamp an
invalid negative count to zero. A separately audited lower bound can omit an
entire inconsistent new object contribution only while preserving the valid
baseline, all original denominator identities and the rejected raw capture.

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
tests exercise their stated API contracts. The selected public subset contains
55 added functions; known failing local regressions are separate issue evidence.

# Scope and interpretation

These tools test the selected binary and record its configuration and hashes.
Their presence does not establish that every Vampire input, option interaction
or build configuration has been tested. Native Windows, macOS, other
architectures and arbitrary external corpora need separate qualification.

The Python harness checks are tests of the runner and its validators. C++ test
functions, solver input cases and reruns under different profiles are separate
counts. A completed run is not necessarily a passing run. Failures and
inconclusive results remain visible with their evidence.

Existing CTest registrations and the upstream sanity script are retained.
The corpus adapter checks literal sanity assertions; it does not replace the
shell script's timing, loop or trace-replay contracts. Run performance-sensitive
sanity checks on an idle machine.

Independent oracles cover bounded propositional formulas, small finite
structures, exact arithmetic identities, datatype graphs, finite-model
certificates and propositional interpolation. Higher-order logic, induction,
polymorphism, unification and simplification also have selected regressions;
those are not general semantic certification.

Vampire round trips can miss errors shared by both solver executions. Parsing
an option does not show that its implementation ran, and a positive activation
counter proves only that the operation occurred. Emitted SMT obligations do
not certify omitted rules or arbitrary complete proofs. The finite-model
checker accepts its bounded single-sort fragment, not arbitrary TPTP models.

The feature map is in [FEATURE_CHECKLIST.md](FEATURE_CHECKLIST.md). Broader
assurance still needs suitable independent oracles, grammar-aware fuzzing with
minimization, mutation tests, answer/synthesis validation, larger corpora and
further resource/concurrency configurations.

The added native subset has 55 functions. At the qualified Z3-enabled
configuration, these accompany 1,981 original functions in 111 registered
suites. Ten further local native regressions that exposed defects are kept
for separate issue/fix work. Removing them from this publication subset does
not change their recorded failures.

Debug cleanup, ASan/LSan, UBSan and Valgrind use separate builds and retain
semantic and memory outcomes independently. A logical answer cannot cancel a
memory error. Incomplete leak checks and truncated XML do not prove memory
safety. Optional direct API probes do not establish a solver CLI trigger.

Coverage includes the compiled Vampire implementation, debug support, bundled
Minisat and SATSubsumption. It excludes test sources and separately maintained
CaDiCaL, VIRAS, Z3 and mini-GMP code, generated build output and system headers.
Code omitted by configuration has no counters in that build. Named functions,
source-location function groups, lines and raw branches remain separate
metrics. Different binaries can have different template denominators.

Raw gaps stay visible. A build-specific reachability proof is separate from
raw coverage; difficult, unsupported or buggy paths cannot be excluded merely
to reach a percentage. Reject invalid counters and preserve failed captures.
Any derived lower bound must retain its denominator and state which new
contribution was omitted. It is not a complete raw campaign capture.

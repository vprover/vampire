# Feature and risk checklist

Use this map to review the selected test scope. It is not a claim that a
coverage percentage or a finite suite establishes Vampire's correctness.

| Area | Checks | Limit |
| --- | --- | --- |
| Existing behavior | CTest, literal sanity assertions and the unchanged shell suite | Timing and build configuration matter |
| Propositional logic | Clause subsets and Boolean expressions with truth tables | Bounded variables and expressions |
| Quantifiers and finite functions | Small explicit relations/functions and known SAT witnesses or contradictions | Bounded structures and formula families |
| Parsing and arithmetic | Valid/rejected syntax, numeric boundaries and exact integer/fraction expectations | Unsupported valid syntax is recorded separately |
| Datatypes | Constructor witnesses and strict-height contradictions | Some solver modes remain incomplete |
| Model and proof output | Bounded emitted-model checks and propositional interpolation/SMT obligations | No general model or whole-proof certification |
| Transformations | Renaming, order/duplicate controls and TPTP round trips | Round trips reuse Vampire |
| Options and schedules | Catalogue parsing, selected combinations and explicit process contracts | Parsing/dispatch does not prove all feature behavior |

For each selected run, preserve commands, inputs, expectations and settings.
Account for cases once, retain interrupted attempts, and classify failures
without turning diagnostic stack counts into defect counts. Harness checks
must pass; solver failures and incomplete checks must remain visible.

See [README.md](README.md) for commands and [SCOPE.md](SCOPE.md) for gaps.

The native layer adds independent set, graph/component, edit-distance and
congruence checks alongside schedule and unification contracts. Its finite
term universes and API calls do not certify every inference rule or establish
an ordinary command-line trigger for an API failure.

The instrumentation layer adds memory checks, configuration validation and
coverage evidence. Retain every raw missed location, every incomplete memory
check and every failed counter capture. The optional API probes are outside
the passing native subset and can reproduce known defects.

Raw coverage is informational by default. A requested numeric gate is an
extra constraint, not a replacement for reviewing important feature gaps and
non-passing tests. General proof/model certification, grammar-aware fuzzing,
mutation tests, synthesis/answer checks and additional platforms remain
future work.

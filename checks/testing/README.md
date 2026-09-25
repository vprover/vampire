# Vampire testing methods

This directory contains testing methods shared for review. It changes test
code and reporting, with production fixes handled separately. The tools save
the commands and evidence needed to inspect a result. A finished run may
contain failures or inconclusive checks.

## Quick start

Run from the repository root on Linux or WSL with Python 3.10 or later,
CMake and a C++20 compiler. Initialize CaDiCaL and VIRAS. Z3 is needed for the
Z3-specific tests and the full recorded suite inventory; configure its CMake
package through `Z3_DIR` if it is not detected automatically.

```sh
git submodule update --init cadical viras
cmake -S . -B build/testing/debug -DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON
cmake --build build/testing/debug --target vampire vtest -j4
python3 -m unittest discover -s checks/testing -p 'test_*.py'
```

Run the existing registered unit suites and inspect non-passing results:

```sh
python3 checks/testing/run.py run --build build/testing/debug --suite units \
  --jobs 2 --timeout 180 --output build/testing/results/unit-check
python3 checks/testing/report.py build/testing/results/unit-check --failures --commands
```

## Existing tests

`units` runs the suites registered by CTest in the selected build. `corpus`
imports literal assertions from `checks/sanity`. `sanity` runs that unmodified
shell script, including timing-sensitive checks; use an otherwise idle machine
and a Release binary. `all` selects this layer's available non-sanity suites.
The existing upstream unit tests and sanity script remain intact.

## Read and resume a run

Choose a fresh output directory for each new run. `summary.json` contains
the totals; `results.jsonl` records completed cases as the run progresses.
`terminal.log` retains the section summaries, and `failures.txt` lists all
non-passing cases with reproduction commands. Each case directory contains
`command.json`, `stdout.log`, `stderr.log` and `result.json`.

A wrong answer, assertion or memory diagnostic fails its check. A timeout,
unsupported obligation or incomplete instrumentation remains inconclusive.
Failed and inconclusive cases make the runner exit nonzero. An explicitly
expected rejection or operational response has its own narrower contract.

Repeat the exact original command with `--resume` only when continuing an
interrupted run. The runner validates saved inputs, binary hashes, harness
and settings, and retains completed failures. Use `--verbose` to print passing
cases too. Close `report.py --watch` without stopping the runner.

## Generated solver checks

The generated suites use bounded truth tables, finite relations/functions,
exact arithmetic and explicit datatype witnesses or contradictions. Further
checks evaluate emitted finite models and propositional interpolants.
[COVERAGE_EXPANSION.md](COVERAGE_EXPANSION.md) describes the oracles and their
limits. Option parsing, feature activation and Vampire round trips have
separate, narrower guarantees.

Start with a partial generated smoke run:

```sh
python3 checks/testing/run.py run --build build/testing/debug --suite generated \
  --limit 12 --jobs 2 --output build/testing/results/generated-smoke
python3 checks/testing/report.py build/testing/results/generated-smoke --failures --commands
```

Omit `--limit` for that complete suite. Other suite names are `features`,
`edges`, `options`, `behavior`, `parsers`, `modes`, `portfolios`, `arithmetic`
and `datatypes`. `--suite all` selects every available non-sanity suite.
`--filter` selects case names; report filtered and limited runs as partial.
The seed is fixed and saved; `--seed` selects another reproducible corpus.

Z3 must be on `PATH` for emitted SMT proof-obligation checks, or supplied
through `--z3`. Unsupported proof rules remain inconclusive. A successful
obligation check does not certify omitted proof steps or an arbitrary whole
proof. [parser-capability-notes.md](parser-capability-notes.md) distinguishes
malformed input from standard syntax that Vampire currently rejects.

## Added C++ tests

The native layer contains all 65 added functions across seven suites: SharedSet,
IntUnionFind, StringUtils, Schedules, UnificationWithAbstractionModes,
SimpleCongruenceClosure and SimpleCongruenceClosureModels. With the Z3-enabled
configuration used for qualification, the full inventory is 2,046 functions
across 111 suites. Conditional compilation can change the available inventory.

In the previous Debug qualification on production revision
`af03e1547d9381cea97c051ed65a7918d07a2b0e`, all 1,981 original functions passed.
The added functions had 55 passes and ten failures. Those ten regressions are
included in the default native suite. They remain ordinary failures, with no
skip or expected-failure setting. CTest reports the three affected suites as
failed; the `vtest` output identifies each failing function.

These tests use the existing `UnitTests` framework and CTest:

```sh
cmake --build build/testing/debug --target vtest -j4
ctest --test-dir build/testing/debug --output-on-failure
build/testing/debug/vtest run SharedSet
build/testing/debug/vtest run StringUtils empty_string_is_not_an_integer_numeral
```

The last command runs one known failure directly. CTest stores its log at
`build/testing/debug/Testing/Temporary/LastTest.log`. The Python `units` runner
above also saves commands and per-suite logs. A nonzero result is expected
while the reported defects remain.

The ten failing functions are grouped below: four StringUtils checks, three
UWA mode checks and three SimpleCongruenceClosure model checks. These are the
recorded results of the previous qualification, not a new run on every build.

| Suite | Failing functions | Report |
| --- | --- | --- |
| StringUtils | `empty_string_is_not_an_integer_numeral`<br>`empty_string_is_not_a_decimal_numeral` | [#997](https://github.com/vprover/vampire/issues/997) |
| StringUtils | `replace_char_preserves_embedded_nul_and_remaining_bytes`<br>`sanitize_suffix_is_independent_of_previous_calls` | [#998](https://github.com/vprover/vampire/issues/998) |
| UnificationWithAbstractionModes | `uwa_constant_reflexive_index` | [#999](https://github.com/vprover/vampire/issues/999) |
| UnificationWithAbstractionModes | `uwa_ground_rejects_open_left`<br>`uwa_ground_rejects_open_right` | [#1000](https://github.com/vprover/vampire/issues/1000) |
| SimpleCongruenceClosureModels | `two_live_instances`<br>`two_live_orderings`<br>`surviving_second_instance` | [#1001](https://github.com/vprover/vampire/issues/1001) |

The StringUtils issues qualify their empty-input and embedded-NUL contract
expectations. The UWA and model cases are API or option-policy findings;
these native failures alone do not establish a wrong solver answer.

## Instrumented profiles

Install Valgrind, GCC with matching `gcov`, and lcov/genhtml. GCC 15 needs
lcov 2.5 or later for these captures. The ordinary profiles require an available
Z3 CMake package; `no-z3` deliberately disables it. A separately built Z3
library is outside Vampire's sanitizer and coverage instrumentation.

`build.sh` checks generated build flags before compiling. Profiles are
`release`, `debug`, `memcheck`, `asan`, `ubsan`, `no-z3` and `coverage`, with
separate directories below `build/testing`. All Debug profiles enable cleanup.

Run a partial Valgrind smoke test:

```sh
JOBS=4 bash checks/testing/build.sh memcheck
python3 checks/testing/run.py run --build build/testing/memcheck --suite generated \
  --limit 12 --memcheck --jobs 2 --timeout 180 \
  --output build/testing/results/valgrind-smoke
python3 checks/testing/report.py build/testing/results/valgrind-smoke --failures --commands
```

Valgrind checks child-process XML too. Invalid accesses, uninitialized reads,
and definite, indirect or possible losses fail memory checks. Reachable records
remain visible without counting as lost. No project suppression file is used.
Timeout-truncated XML cannot establish a clean memory check.

For ASan, build `asan`, select that build, and pass `--asan`; the runner keeps
leak detection and separates reported diagnostics from incomplete leak checks.
`--sanitizer-error-grace 10` bounds the wait after an actual sanitizer error
without turning it into a pass. Use `ubsan` for undefined-behavior checks.

For a fresh coverage build, run a partial test selection and then capture only
after all instrumented processes have exited:

```sh
JOBS=4 bash checks/testing/build.sh coverage
python3 checks/testing/run.py run --build build/testing/coverage --suite generated \
  --limit 12 --jobs 2 --output build/testing/results/coverage-smoke
python3 checks/testing/coverage.py --build build/testing/coverage \
  --output build/testing/results/coverage-report
```

Open `build/testing/results/coverage-report/html/index.html`. The same directory
contains `coverage.info` and machine-readable gaps. Counters accumulate: use a
fresh build for a new baseline, or preserve earlier counters and use the
[coverage overlay](coverage-overlay.md). Do not mix builds or reset previous
evidence to make a new report. Coverage errors fail capture. If LCOV rejects
overlapping function ranges, inspect them before explicitly choosing
`--allow-overlapping-functions`; that choice is recorded.

## Campaigns and optional probes

After the small runs, a campaign builds and executes the selected profiles:

```sh
python3 checks/testing/campaign.py --profiles release memcheck \
  --jobs 4 --memcheck-jobs 2 --output build/testing/results/campaign
```

Omit `--profiles` for the complete configured profile set. A selected subset is
a partial campaign. `campaign.json` records every stage; stage directories
contain their summaries and logs. Independent stages continue after failures.
Use `--resume` with identical settings to continue an interrupted campaign.
Raw coverage is informational unless `--require-coverage-percent N` is set.
Every gap remains reported, and an optional threshold does not establish
general correctness.

[OPTION_BEHAVIOR.md](OPTION_BEHAVIOR.md) documents the 47 runtime-option cases
and their observed activation requirements. [API_PROBES.md](API_PROBES.md)
documents optional isolated C++ destruction/cache probes. They remain
available separately from the 65 registered native functions and are outside
the default campaign. Their known failures and inconclusive cases remain
visible when the probes run.

See [SCOPE.md](SCOPE.md) for the measurement limits.

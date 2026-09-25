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

See [SCOPE.md](SCOPE.md) for the measurement limits.

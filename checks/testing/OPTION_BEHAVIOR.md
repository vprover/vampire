# Runtime option behavior

`runtime_options.py` runs 47 bounded cases for ten options. Each case checks
the solver's answer against a truth table or a stated logical reduction.
Enabled settings also require a positive inference counter, preprocessing
marker, or finite-model size trace. These checks use `run.run_case`,
`diagnostics.combine`, and `finite_model_validation.check_model` from this
directory.

| Option | Independent answer check | Activation evidence |
| --- | --- | --- |
| `blocked_clause_elimination` | A blocked pair plus SAT/UNSAT ground clauses; complete truth table | Positive blocked-clause counter |
| `equality_resolution_with_deletion` | `X!=a OR p(X)` forces `p(a)`; a singleton witnesses SAT | Positive equality-resolution counter and deletion preprocessing marker |
| `general_splitting` | Instantiate `p(X) OR q(Y)` at the two ground negative units; a singleton witnesses SAT | Positive general-splitting counter |
| `inequality_splitting` | An equation makes the paired disequality false, forcing `p` | Positive split-inequality counter |
| `predicate_elimination` | Complete two-atom truth tables; a separate universal multi-occurrence clause contradicts its ground negative instance | Positive eliminated-predicate or generated-resolvent counter |
| `unused_predicate_definition_removal` | Extend any model of the ground truth table with the unused predicate's definition | Positive unused-definition counter |
| `condensation` | Taking `X=Y` in `p(X) OR p(Y)` forces universal `p` | Positive condensation counter for `fast` and `on` |
| `inner_rewriting` | `f(a)=a` reduces the paired clause to `p(a)` | Positive inner-rewriting counter |
| `unit_resulting_resolution` | Complete truth table of a Horn implication and its antecedents | Positive unit-resulting-resolution counter |
| `fmb_start_size` | Exactly two elements, a swapping unary function, and identity relation; emitted model independently validated | Requested initial size and complete attempted-size trace |

The quantified and equality UNSAT reductions follow directly from the input;
they do not infer general UNSAT from a bounded domain search. Every SAT input
has a finite witness. The finite-model checker covers this fixture's fragment,
including its function and relation tables.

There are 27 required activation checks and 19 disabled controls. One case,
`predicate_elimination-multi-occurrence-on`, checks the answer without requiring
activation: ordinary predicate elimination does not handle that input, although
resolution can solve it. Its activation stays `inconclusive` when no counter
appears. The `multi` setting must generate a predicate-elimination resolvent.

A positive counter only establishes that the named operation occurred. A
logical pass, an observed activation, and a memory failure can coexist in the
same result. Memory failures remain failures.

## Run the checks

Run from the checkout root with Python 3.10 or later:

```sh
python3 -m unittest discover -s checks/testing -p test_runtime_options.py -v
python3 checks/testing/runtime_options.py \
  --build build/testing/release --profile release \
  --output build/testing/runtime-release
```

`--build` accepts a build directory or an executable path, including a binary
from another checkout. `--profile` accepts `release`, `debug`, `coverage`,
`no-z3`, `asan`, `ubsan`, or `valgrind`. Select the profile that matches the
binary. Profiles do not build or alter the binary. Valgrind uses a Debug binary
and requires `valgrind` on `PATH`.

The default is two workers, a five-second solver limit, and a 120-second outer
limit per case. `--jobs`, `--timeout`, and `--filter` change those settings.
Valgrind disables the solver timer and retains the outer limit. ASan removes
Vampire's default address-space cap and enables leak detection unless
`ASAN_OPTIONS` is already set. The effective environment is recorded.
`--sanitizer-error-grace` forwards the diagnostic deadline to the process
runner; the campaign sets it for ASan.

The output directory must be new. It contains exact inputs and commands,
stdout/stderr, memory diagnostics, per-case results, and a summary. Metadata
records the binary hash before and after execution, version output, source
checkout revision and status, current tracked C++/header/CMake hashes, CMake
cache hash, harness revision, and copied harness sources with hashes. A
source checkout's current revision is provenance data, not proof of which
revision produced an arbitrary externally supplied binary.

The command returns zero only when every selected case passes its required
checks and the binary hash is unchanged. Wrong answers, memory errors,
timeouts, incomplete instrumentation, and missing required activation produce
a nonzero exit. An empty filter selection is an error. The declared ordinary
predicate-elimination exception does not fail the suite.

The callable interface is:

```python
run_suite(build, profile, output, *, jobs=2, timeout=120,
          pattern='', sanitizer_error_grace=None)
```

It returns the same dictionary saved in `summary.json`, including `exit_code`.
The campaign runs this stage for each selected profile before coverage capture.
An interrupted stage is preserved as an earlier attempt before it is restarted.

## Audit option use

```sh
python3 checks/testing/runtime_options_audit.py \
  --run build/testing/campaign/release-all \
  --extension build/testing/runtime-release \
  --output build/testing/runtime-option-audit.json
```

Pass the ordinary runner's result directory to `--run`; it must contain
`option-inputs/catalogue.json` and `summary.json`. Repeat `--extension` for
other runtime-option result directories.

The audit separates parser checks, explicit solver commands, and observed
activation. Help, option discovery, transformations, expected rejection, and
other output-only commands do not count as solver use. Exact SMT answer
checks, including the unsat-core case, do count. Defaults, encoded strategies,
secondary round-trip commands, and shell scripts are not expanded. Command
presence alone does not establish option acceptance or activation.

## Harness checks

The unit tests exercise activation requirements, independent answers, invalid models, instrumentation outcomes and audit classification. Run the command above against this checkout; historical campaign results do not validate a newly built binary.

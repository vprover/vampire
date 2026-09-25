# Extending coverage without changing the baseline

`coverage_overlay.py` runs on Linux or WSL with the GCC tools that produced the instrumented build. It writes new counters under a fresh `GCOV_PREFIX` directory. `GCOV_PREFIX_STRIP=0` retains the full embedded build path below that directory. The helper copies `.gcno` files and hashes the existing `.gcda` files, solver binaries, source files in the saved trace, and the trace itself. It checks those inputs before and after execution and capture.

Use the source directory embedded in the existing build, even when the test harness lives in another worktree. The saved trace must describe the current frozen counters, with the same source filters and instrumentation settings.

```bash
python3 checks/testing/coverage_overlay.py prepare \
  --build /absolute/original/build/testing/coverage \
  --source /absolute/original/source \
  --baseline-trace /absolute/existing/coverage.info \
  --output /absolute/fresh/overlay \
  --tool-dir /absolute/lcov/bin \
  --allow-overlapping-functions

python3 checks/testing/coverage_overlay.py run \
  --output /absolute/fresh/overlay --timeout 3600 -- \
  /absolute/original/build/testing/coverage/vampire --help

python3 checks/testing/coverage_overlay.py capture \
  --output /absolute/fresh/overlay
```

Replace the command after `--` with the desired test runner invocation. The timeout covers that whole command. Use `--gcov-tool` and `--gcov-merge-tool` at prepare time when matching GCC tools have versioned names. `--allow-overlapping-functions` disables LCOV's cross-metric consistency check; use it only when the original trace used that setting. The helper does not reset counters or rebuild the solver.

Capture copies the frozen baseline counters into a separate tree, adds the overlay counters with `gcov-tool merge`, and captures the combined counters. It verifies the exact sum for every object-local function, line, and basic-block branch in gcov JSON. Those raw identities retain template instances that LCOV can fold together. The JSON files and their hashes remain in the output.

LCOV is run separately on the copied baseline and combined counters. The copied baseline must reproduce the historical trace's totals and source coverage, including the branch count per source line and branch type. The fresh baseline and combined trace must have identical line, named-function, function-group, and branch identities. Previously hit entries cannot disappear. `capture/delta.json` reports the denominator and added hits for each metric; `capture/coverage.info` is the cumulative trace. `capture/raw-union.json` reports the separate object-local denominator and verifies every counter sum.

The historical LCOV trace is retained without adding it again. A smoke experiment found that adding sparse LCOV traces could change template representatives and even lose a recorded hit. The raw-counter merge avoids that source-level merge. Any difference between historical and recaptured branch labels is recorded in `historical_branch_identity_symmetric_difference`; the frozen raw counters and exact object-local sum establish provenance.

The overlay must be idle for another run or capture. A timed-out, interrupted, or abnormal wrapper run makes the overlay unusable for further automation. Preserve it for review and prepare a fresh overlay. A normal launcher exit with a live process that inherited the overlay destination is also rejected. This is a coverage workflow guard, not a filesystem sandbox for arbitrary commands.

All raw logs and failed captures are retained. Capture accepts a fresh output only; a failed capture is not overwritten. Helper source snapshots and tool hashes identify the implementation used by each operation. No exception, assertion, compiler-generated, defensive, or uncovered branch exclusions are added. The original source filters exclude the existing unit-test and dependency directories.

The branch denominator can contain compiler-generated edges that cannot execute in the fixed object code. Coverage improvements should be measured against the retained denominator. A claim of literal 100% requires an argument that every recorded edge is reachable; a source-line count alone does not establish that. See [GCC's counter relocation documentation](https://gcc.gnu.org/onlinedocs/gcc/Cross-profiling.html) and [gcov's JSON format](https://gcc.gnu.org/onlinedocs/gcc/Invoking-Gcov.html).

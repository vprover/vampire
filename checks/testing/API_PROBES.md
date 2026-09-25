# Optional isolated C++ API probes

These probes exercise SAT-inference destruction, Boolean-term destruction
with a heap-backed label, and cached clause counts after adding units. They
can reproduce known failures or inconclusive timeouts against the tested
upstream implementation. They are outside the passing 55-function native
subset and are not part of the default campaign. No ordinary solver CLI
trigger follows from a direct API test.

## Prepare and inspect

Use Linux/WSL with Python 3.10 or later and a completed Debug build produced
by CMake's Unix Makefiles generator. The runner requires `vampire`, `vtest`,
exported compiler commands and `CMakeFiles/vtest.dir/link.txt`. It rejects
unsupported wrappers, response files, coverage, LTO and unrecognized flags.

```sh
cmake -S . -B ../vampire-api-debug -G 'Unix Makefiles' \
  -DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
cmake --build ../vampire-api-debug --target vampire vtest -j4
python3 checks/testing/api_probes.py --build ../vampire-api-debug \
  --output ../vampire-api-plan --plan-only
```

Read `../vampire-api-plan/metadata.json` before executing the plan. Each output
directory must be fresh and outside the baseline source and build directories.
Keep the baseline idle: the runner reuses compiled objects and checks its
recorded inputs before and after execution. It does not configure or rebuild
that baseline. Current source hashes record provenance; they cannot prove the
origin of arbitrary pre-existing object files.

## Execute

```sh
python3 checks/testing/api_probes.py --build ../vampire-api-debug \
  --output ../vampire-api-native
python3 checks/testing/api_probes.py --build ../vampire-api-debug \
  --output ../vampire-api-valgrind --memcheck --timeout 90
```

The second command requires Valgrind on `PATH`. The runner copies two fixtures,
compiles separate objects and links an isolated probe executable. Objects,
compiler/linker dependency files and the executable are written only below
the selected output directory. Commands, logs and per-probe results accompany
`summary.json`; `metadata.json` records provenance and rewritten commands.

Successful destruction requires the completion marker and a zero exit. The
count probe requires cached and actual counts to agree. An invalid free or
wrong count remains a failure. A destructor timeout without an access-error
diagnostic remains inconclusive; missing/truncated Valgrind XML is not evidence
of an invalid access or a clean memory check. Separate leak records remain
visible. Failed or inconclusive checks give a nonzero command exit.

Harness checks for the isolated runner are available independently:

```sh
python3 -m unittest discover -s checks/testing -p test_api_probes.py -v
```

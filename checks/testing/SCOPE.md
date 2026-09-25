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

# Vampire

This is a brief introduction to this repository. Please see <a href="https://vprover.github.io/">the Vampire website</a> for more general information about Vampire. Please see LICENCE for usage restrictions. Note that Vampire makes use of minisat and z3 and some of this code is included in this codebase, such code is provided under their own licence.

Found a bug? Have a feature request? Please use the GitHub Issues tab for these.

## Making

There is a nice Makefile. You can make
 * vampire_dbg for a debug version 
 * vampire_rel for a release version
 * vampire_z3_rel to build with z3 (also works with debug) but for this you will need a z3 binary in include to link against
 * vampire is a shortcut for vampire_dbg that doesn't rely on git commands - use this if you download Vampire as a zip file
 * clean to clean things up

You can also make
 * vtest for a set of unit tests. Run vtest -ls for help once compiled
 * vampire_gcov for a version with coverage information
 * vampire_static for a statically linked version, necessary for portability
 

## Some notes for developers

Please do not work on master! 

The main top level file is vampire.cpp. This is the head of the main vampire executable. The main method parses options and checks the mode.

Other top level files include vX.cpp (i.e. vclausify.cpp) these are cut down versions of vampire that are not currently maintained. They run a single mode of vampire. If you want to do this you might need to fix them based on vampire.cpp. The vtest.cpp file works for unit testing.

There are some other top-level files that are left over from previous use cases. Some of described below under Scripts, others may be cleaned up at a later date.

Note that Forwards.hpp contains a lot of forward declarations of things.

### Namespaces

The code is organised into a number of namespaces. Here is a brief overview.

The core of Vampire is defined in: 
 * Kernel contains the core prover-related structures
 * Lib contains the main generic data structures (also Allocator for memory allocation)
 * Shell contains things that help perform proofs, including preprocessing
 
Vampire mode is implemented using
* Indexing
* Inferences
* SAT contains SAT solvers for use in various places
* InstGen, see IGAlgorithm
* Saturation, see SaturationAlgorithm (and Splitter for AVATAR)
* Tabulation, see TabulationAlgorithm

Other key namespaces are
 * CASC
 * Debug 
 * Parse
 * UnitTests

Other namespaces have specific purposes that you will find out by looking at them.

### Documentation

Running make doc makes documentation using doxygen; this has not been fully maintained but ideally each function and class would have an appropriate comment to be parsed by doxygen. 


### Scripts

There are some scripts that might be useful. This list can be expanded:
 * dogcov.sh produces coverage data when running vampire_gcov
 * vinter is a front-end script for that tool
 * runner.sh and ltb_mode are scripts that have been used to run vampire in the past

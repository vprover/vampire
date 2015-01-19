# Vampire

This is a brief introduction to this repository. You will increase the liklihood of understanding things if you get your hands dirty and give things a poke.

Do not work on the master branch - if you want to play create your own branch.

## Making

There is a nice Makefile. You can make
 * vampire_dbg for a debug version - this is usually the first thing you will do
 * vampire_rel for a release version
 * clean to clean things up
You can also make
 * vtest for a set of unit tests. Run vtest -ls for help once compiled
 * vampire_gcov for a version with coverage information
 * vampire_static for a statically linked version, necessary for portability
 

## Top level files

The main top level file is vampire.cpp. This is the head of the main vampire executable. The main method parses options and checks the mode.

Other top level files include vX.cpp (i.e. vclausify.cpp) these are cut down versions of vampire that are not currently maintained. They run a single mode of vampire. If you want to do this you might need to fix them based on vampire.cpp. The vtest.cpp file works for unit testing.

There are some other top-level files that are left over from previous use cases. Some of described below under Scripts, others may be cleaned up at a later date.

Note that Forwards.hpp contains a lot of forward declarations of things.

## Namespaces

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

## Documentation

Running make doc makes documentation. It would also be nice to use the GitHub wiki pages to document things such as coding style.

There are (unmaintained) 'explanation' files in each directory that might contain additional explanation.

## Scripts

There are some scripts that might be useful. This list can be expanded:
 * dogcov.sh produces coverage data when running vampire_gcov
 * vinter is a front-end script for that tool
 * runner.sh and ltb_mode are scripts that have been used to run vampire in the past

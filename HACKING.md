# Hacking Vampire
Welcome, new (or "experienced"!) Vampire developer.
We've compiled some information below to help you on your way.

## Team
The [team page](https://vprover.github.io/team.html) is kept somewhat up-to-date.
You should add yourself by following the instructions in the [website repository](https://github.com/vprover/vprover.github.io)!
Team discussion currently happens on [Slack](https://vampireglobal.slack.com) - hang out there and ask questions.

## Reading Vampire
Vampire is not always easy to read, especially with acronyms like `FMB`, `LTB`, `CASC` scattered about as well as the usual theorem-proving nonsense words like "superposition".
Hopefully talking to the team can help you, but the following gives some pointers.

### Doxygen
Vampire can use [Doxygen](https://www.doxygen.nl/index.html) to generate documentation from comments in its source files.
Run `doxygen` in the root to generate the documentation files as HTML.
Not all parts of Vampire are well-documented; if you figure out how a class or function works it's well worth commenting it, preferably in Doxygen syntax.

### Directories and Namespaces
Namespaces roughly correspond to directories, and classes to files, but not exactly.
Many of us use a navigation tool like `ctags` or an IDE to get about.
In a pinch, `git grep PAT` works OK too.
* `CASC/` implements special routines for [CASC](http://www.tptp.org/CASC/)
* `Debug/` provides debugging utilities like assertions and tracebacks
* `Test/` contains various utilities for unit testing, as well as the main functions to integrate `UnitTests/` with `ctest`.
* `UnitTests/` contains one testing unit per file. See the section on testing for details.
* TODO something about each directory please (even if just "unused")

### Vampire idioms and quirks
* `CALL` macros at the start of most functions implement a call stack in debug mode, among other things (see `Debug/Tracer`).
 Every non-trivial function (i.e. probably not getters/setters, but most other things) should do this: if you find one without it's a good first patch!
 `CALL` is a no-op in release builds.
* `ASS` and friends are debug-only assertions, defined in `Debug/Assertion`.
  No donkeys here.
* Heavy use of "iterator" classes which can do slightly odd things. These are in the process of being re-organised somewhat by Joe.
* Some amount of unused/dead code. If it looks like nonsense, doesn't compile, or isn't reachable, it might well just not be used any more. Pull requests appreciated.
* A (possibly slightly outdated) explanation for the message [Attempted to use global new operator, thus bypassing Allocator!](https://github.com/vprover/vampire/wiki/Attempted-to-use-global-new-operator,-thus-bypassing-Allocator!)
* for historians: [Yes, we had (and still have) a wiki on our github page](https://github.com/vprover/vampire/wiki) - maybe miscellaneous things can go here, I don't think it's completely historic just yet! - Michael
* TODO more tips

## Building with CMake
If you don't know [CMake](cmake.org), we suggest you take a little time to learn how to [use CMake builds](https://cmake.org/cmake/help/latest/guide/user-interaction/index.html) and a little about how to [write CMake build scripts](https://cmake.org/cmake/help/latest/guide/tutorial/index.html).
Vampire uses a relatively-simple CMake build, so you can read `CMakeLists.txt` if you like to figure out how it works.
Generally you should only need to touch the build system to add new files and un-break builds; ask the team if something isn't working for you.

### Build Options
All build options are controlled as additional arguments to CMake.
For example, `cmake -DEXAMPLE=value ..`, or you can use a GUI tool if you prefer.
Notable options are:
* Debug build: `-DCMAKE_BUILD_TYPE=Debug`
* Target directory: `-DCMAKE_INSTALL_PREFIX=/opt/vampire-devel` - helpful when compiling z3 to avoid collisions with other installed versions.
* Static compilation: `-DBUILD_SHARED_LIBS=0`
  This option only prefers static libraries over shared libraries which can
  lead to a mixed binary.
  You can check the output of the linking which libraries were not linked in.
  Please be also aware that Mac OS X does not support completely statically linked libraries (see also Apple's [Technical Q&A](https://developer.apple.com/library/archive/qa/qa1118/_index.html)).
* "Inter-Procedural Optimisation": `-DIPO=ON`. This enables potentially-expensive linker options (depending on your system) which may produce a small performance improvement. Probably only useful for competitions.

### Z3
We fix a known version of Z3 via `git-submodule`.
If you don't need Z3, do nothing: CMake will detect this and do the right thing.
If you need Z3, first `git submodule update --init` to pull the correct version of Z3, then build Z3 via its own CMake system into `z3/build`, which is where Vampire's CMake will find the necessary files.
CMake will then detect this build and do the right thing.

Do _not_ commit changes to the toplevel `z3` folder unless you mean to change the fixed version of Z3 we build with.
If you do want to do this, do it _carefully_, make sure you know [how submodules work](https://git-scm.com/book/en/v2/Git-Tools-Submodules), then warn the team after merging so that they can update their submodule builds and look for introduced bugs.

#### Advanced Z3
* If you've used Z3 in the past but don't want it for this build, pass `-DCMAKE_DISABLE_FIND_PACKAGE_Z3=ON` to disable automatically including Z3.
* If you want to override the Z3 search path, first think carefully about whether you need to do this: Z3 is a fixed submodule for a reason! Then remove `CMakeCache.txt` if present (the path to Z3 is cached) and pass `-DZ3_ROOT=/foo/bar/build/`.
* To make sure CMake found the intended package, pass `-DCMAKE_FIND_DEBUG_MODE=ON`

#### Building Z3
Please refer to Z3's [CMake documentation](https://github.com/Z3Prover/z3/blob/master/README-CMake.md). Notable options are:
* `-DZ3_BUILD_LIBZ3_SHARED=0`: static library
* `-DCMAKE_INSTALL_PREFIX=/opt/z3-devel`: installation path

### Building for competitions
TODO how do we build for competitions?
E.g. details of build configuration, linking, Spider?

### CMake tips'n'tricks
* Verbose compilation for UNIX Makefiles: if you would like to disable the progress reports and see the commands that are run, call `make VERBOSE=1`.

## Testing with CTest
Vampire now has units tests which can run with CTest.

### Running tests
tl;dr:
(test are only compiled in Debug mode)
```
mkdir cmake-build
cd cmake-build 
cmake -DCMAKE_BUILD_TYPE=Debug ..
make 
ctest --output-on-failure
```

Unit test binaries are automatically built when building with cmake. They can be run by calling `ctest` in the build directory. 

Options you will probably find useful are the following:
* `--output-on-failure`
* `--rerun-failed`
* `-R <regex>` run only tests with names matching `<regex>`
* `-E <regex>` do not run tests with names matching `<regex>`

Every test unit consists of multiple test cases, which will be run each as a separate process. This can be annoying if one wants to debug a single test case using `lldb` or similar tools. Therefore you can also run a single test case without launching a separarate process:
```
mkdir cmake-build
cd cmake-build
cmake ..
make 
./vtest run <unit_id> <test_case>
```
All available test cases and test units can be listed with 
```
./vtest ls
```

Compiling tests can also slow down compile times. Compiling them can be circumvented by calling `make vampire` instead of `make` in your cmake directory.


### Creating new unit tests
tl;dr: 
```
# choose a name
MY_TEST_NAME=...

# create test file
cp UnitTests/tSyntaxSugar.cpp UnitTests/t${MY_TEST_NAME}.cpp

# alter CMakeLists.txt
sed -e "{/tSyntaxSugar.cpp/p;s/tSyntaxSugar.cpp/t${MY_TEST_NAME}.cpp/;}" \
    -i '' CMakeLists.txt

# write the unit test
vim UnitTests/t${MY_TEST_NAME}.cpp
```

The unit tests are located in the directory `UnitTests/`. The tests are expected to be `cpp` files, and are prefixed with a `t` (e.g.: `UnitTests/tSyntaxSugar.cpp`). Each new test file must be added to the source list `UNIT_TEST` in `CMakeLists.txt`.

A test file must include `Test/UnitTesting.hpp` contain the following statements to initalize unit testing.
```
#include "Test/UnitTesting.hpp"
```

After this test functions can be defined:
```
TEST_FUN(<test_name>) {
  /* testing code goes here */
}
```

Every test function will be run as its own process. It is considered successful if the process exits with code `0`, or the test function returns void, and considered a failure when the process throws an exception, violates an assertion, or exits with code `-1`.


Consider the following guide-lines for writing unit tests:
* what every individual test case does should be visible at first sight
* keep them short and concise
* don't test multiple things in one test
* don't rely on stdout printing of your unit tests. their success is meant to be machine checked.
* for that use and extend the test utilities mentioned in the next section.

### Test utilities

Testing utilities can be found in `Test/`. The most notable are currently (all not yet merged):
- `Test/TestUtils.hpp`, containing utilites like checking equality of terms, literals and clauses modulo AC
- `Test/SyntaxSugar.hpp`, containing utilities to create terms, literals and clauses in a nicely read and writable way
- `Test/GenerationTester.hpp`, framework for writing tests for `SimplifyingGeneratingInference`s and `GeneratingInferenceEngine`s. An example for these tests is given in `UnitTests/tEqalityResolution.cpp`. Pitfully we do not have unit-test for all our old inference rules, as these were not written with unit testing in mind, and are tightly bound to the `Saturation/SaturationAlgorithm.hpp` framework, which will hopefully be resolved by refactoring in the future.
- `Test/SimplificationTester.hpp`, framework for testing `SimplifyingInferenceEngine`s. An example for these tests if given by `UnitTests/tGaussianElimination.cpp`

## Continuous Integration
There is a general build/test/sanity-check script set up to run on GitHub Actions, either manually (go to the "actions" tab) or when a PR is created or updated.
The CI script is located in `.github/workflows`.
Currently it:
 - checks copyright headers in source files
 - builds Z3
 - builds Vampire and links it to Z3 (tacit assumption: more things are likely to go wrong with Z3 than without...right?!)
 - runs unit tests
 - runs a sanity check on the resulting binary

If the build fails for some reason, you can debug it by going through the logs to determine which step failed and with what output. Then...good luck!

## Guidelines for `git`
Vampire uses the `git` VCS.
All changes are made by authorised persons merging branches from others into `master` after review.
`master` should always build and be generally sane, but may not be a stable release.

Try and keep pull requests short and making exactly one change.
This makes it easier for review, to avoid breaking things, and makes _your_ life easier as `master` is less likely to change significantly underneath you.
Many seemingly-large changes can be broken down into smaller steps!
However, there are occasions which justify long-lived branches.

To make a change, start by making a personal branch.
Call it something related to the feature, but also prepend your name to avoid clashes.
For example, `michael-static-assert` removed the old static assertion mechanism in favour of C++11's `static_assert`.
You can then make commits to this branch and create a PR on GitHub when the work in the branch is ready for review.

Commits can be kept tidy by occasionally [rewriting history](https://git-scm.com/book/en/v2/Git-Tools-Rewriting-History), provided nobody is using your branch.
If you have pushed commits to remote and want to rewrite them, you can _carefully_ use `git push --force-with-lease` to push the rewritten commits while not accidentally breaking other people's work.

If `master` changes under you in such a way that you want to reconcile the two (e.g. before a PR), you have two options:
1. `git rebase` rewrites history, roughly pretending that you made changes starting from a later point in the parent branch.
 This keeps commit history neat and is the preferred option if nobody is currently using your branch and if a rebase is feasible.
2. Otherwise, merging `master` into your branch is OK as well and can be easier for large changes.

### On Merge Commits
[Please, oh please, use "git pull --rebase"](https://coderwall.com/p/7aymfa/please-oh-please-use-git-pull-rebase)
This can be even configured [globally](https://coderwall.com/p/tnoiug/rebase-by-default-when-doing-git-pull).
To explain: While it is fine to have merge-commits as a documentation for where a long-lived feature branch joined master
(or where a long lived feature branch had to be synced with master by mergeing with it), 
"git pull --rebase" prevents you from creating a useless merge commit on pulling a branch that your colleague recently modified.
(This can happen, for instance, when someone reviewing your pull request fixes a tiny bug, while you were in the meantime fixing another.)

## General Code Guidelines
* Compiler warnings are there to help you; do not suppress them without Really Good Reasons!
* In the same vein, master should build free of warnings. Pull requests to fix warnings (preferably by not doing the thing the compiler is warning you not to do) are valuable that allows you and others to notice when you introduce code that produces warnings.
* TODO more coding guidelines!

## Vampire-specific guidelines
TODO any Vampire-specific guidelines (gotchas particularly) you can think of.

## Style Guide
Consistent style is important for readability; we do not care particularly what the style _is_, so long as it's consistent.
However, Vampire has had many authors, not all of whom used the same style.
We would like to use an automatic formatting tool to enforce a fixed style, but reformatting the entire codebase at once would break people's branches and also result in a massive diff. [We're looking into this.](https://www.moxio.com/blog/43/ignoring-bulk-change-commits-with-git-blame#git-2.23-to-the-rescue)

Experimentally, the [ClangFormat](https://clang.llvm.org/docs/ClangFormat.html) configuration file found in `.clang-format` matches the current Vampire style relatively well.
Over time, we intend to format the whole codebase this way.
To help with this effort:
* Format all new code automatically (and beautifully!) with `clang-format`
* If automatic formatting isn't feasible for some reason, try and match the existing style.

## PR Checklist
Authors and reviewers, try and ensure the following.

Before merging a PR:
* CI passes with a clean build, free of warnings or test failures (read the build log!)
* Unit tests where reasonable for new functionality (bonus points for unit tests for existing functionality!)
* Doxygen comments where sensible
* Remove code made dead by PR
* Commit history is sane
* Reasonable formatting

## Testing and Benchmarking
TODO what's a reasonable set of problems to run Vampire on to check for introduced bugs?

---

Happy hacking! -- the Vampire team.


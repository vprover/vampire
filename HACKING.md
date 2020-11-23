# Hacking Vampire
Welcome, new (or "experienced"!) Vampire developer.
We've compiled some information below to help you on your way.

## Team
The [team page](https://vprover.github.io/team.html) is kept somewhat up-to-date.
You should add yourself by following the instructions in the [website repository](https://github.com/vprover/vprover.github.io)!
Team discussion currently happens on [Slack](https://vampireglobal.slack.com) - hang out there and do ask questions.

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
In a pinch, `grep PAT $(git ls-files)` works OK too.
* `CASC/` implements special routines for [CASC](http://www.tptp.org/CASC/)
* `Debug/` provides debugging utilities like assertions and tracebacks
* TODO something about each directory please (even if just "unused")

### Vampire idioms and quirks
* `CALL` macros at the start of most functions implement a call stack in debug mode, among other things (see `Debug/Tracer`).
 Every non-trivial function (i.e. probably not getters/setters, but most other things) should do this: if you find one without it's a good first patch!
 `CALL` is a no-op in release builds.
* `ASS` and friends are debug-only assertions, defined in `Debug/Assertion`.
  No donkeys here.
* Heavy use of "iterator" classes which can do slightly odd things. These are in the process of being re-organised somewhat by Joe.
* Some amount of unused/dead code. If it looks like nonsense, doesn't compile, or isn't reachable, it might well just not be used any more. Pull requests appreciated.
* TODO something about the allocator by someone who knows something about it
* TODO more tips

## Building with CMake
If you don't know [CMake](cmake.org), we suggest you take a little time to learn how to [use CMake builds](https://cmake.org/cmake/help/latest/guide/user-interaction/index.html) and a little about how to [write CMake build scripts](https://cmake.org/cmake/help/latest/guide/tutorial/index.html).
Vampire uses a relatively-simple CMake build, so you can read `CMakeLists.txt` if you like to figure out how it works.
Generally you should only need to touch the build system to add new files and un-break builds; ask the team if something isn't working for you.

### Build Optiona
All build options are controlled as additional arguments to CMake.
For example, `cmake -DEXAMPLE=value ..`, or you can use a GUI tool if you prefer.
Notable options are:
* Debug build: `-DCMAKE_BUILD_TYPE=Debug`
* Target directory: `-DCMAKE_INSTALL_PREFIX=/opt/vampire-devel`; helpful when compiling z3 to avoid collisions with other installed versions.
* Static compilation: `-DBUILD_SHARED_LIBS=0`
  This option only prefers static libraries over shared libraries which can
  lead to a mixed binary.
  You can check the output of the linking which libraries were not linked in.
  Please be also aware that Mac OS X does not support completely statically linked libraries (see also Apple's [Technical Q&A](https://developer.apple.com/library/archive/qa/qa1118/_index.html)).

### Z3
We fix a known version of Z3 via `git-submodule`.
If you don't need Z3, do nothing: CMake will detect this and do the right thing.
If you need Z3, first `git submodule update --init` to pull the correct version of Z3, then build Z3 via its own CMake system into `z3/build`, which is where Vampire's CMake will find the necessary files.
CMake will then detect this build and do the right thing.
Finally, if you've used Z3 in the past but don't want it for this build, pass `-DCMAKE_DISABLE_FIND_PACKAGE_Z3=1` to disable automatically including Z3.

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
Vampire now has some units tests which can run with CTest.
TODO @Joe can you write something here?

## Continuous Integration
The Vampire repository is currently setup with GitHub Actions to build `master` every day at `00:00` UTC, or to build a branch when a PR is created or updated.
Additionally, the build can be run manually by going to the "actions" tab in GitHub.

The CI script caches the Z3 build (unless the submodule changes!) and builds a debug version of Vampire from scratch, then runs the unit tests.
Currently it takes around 4-6 minutes for the remote server to build Vampire - if this suddenly takes longer this is worth investigating to preserve the quick-iteration value of the CI script.

## Guidelines for `git`
Vampire uses the `git` VCS.
All changes are made by authorised persons merging branches from others into `master` after review.
`master` should always build and be generally sane, but may not be a stable release.

Try and keep pull requests short and sweet, this makes it easier for review, to avoid breaking things, and makes _your_ life easier as `master` is less likely to change significantly underneath you.
Many seemingly-large changes can be broken down into smaller steps!
However, there are occasions which justify long-lived branches.

To make a change, start by making a personal branch, calling it something related to the feature but also prepending your name to avoid clashes.
For example, `michael-static-assert` removed the old static assertion mechanism in favour of C++11's `static_assert`.
You can then make commits to this branch and create a PR on GitHub when the work in the branch is ready for review.
Commits can be kept tidy by occasionally [rewriting history](https://git-scm.com/book/en/v2/Git-Tools-Rewriting-History), provided nobody is using your branch.
If you have pushed commits to remote and want to rewrite them, you can _carefully_ use `git push --force-with-lease` to push the rewritten commits while not accidentally breaking other people's work.

If `master` changes under you in such a way that you want to reconcile the two (e.g. before a PR), you have two options:
1. `git rebase` rewrites history, roughly pretending that you made changes starting from a later point in the parent branch.
 This keeps commit history neat and is the preferred option if nobody is currently using your branch and if a rebase is feasible.
2. Otherwise, merging `master` into your branch is OK as well and can be easier for large changes.

## General Code Guidelines
* Compiler warnings are there to help you; do not suppress them without Really Good Reasons!
* In the same vein, master should build free of warnings. Pull requests to fix warnings (preferably by not doing the thing the compiler is warning you not to do) are valuable that allows you and others to notice when you introduce code that produces warnings.
* TODO more coding guidelines!

## Vampire-specific guidelines
TODO any Vampire-specific guidelines (gotchas particularly) you can think of.

## Style Guide
Consistent style is important for readability; we do not care particularly what the style _is_, so long as it's consistent.
However, Vampire has had many authors, not all of whom used the same style.
We would like to use an automatic formatting tool to enforce a fixed style, but reformatting the entire codebase at once would break people's branches and also result in a massive diff.

Experimentally, the [ClangFormat](https://clang.llvm.org/docs/ClangFormat.html) configuration file found in `.clang-format` matches the current Vampire style relatively well.
Over time, we intend to format the whole codebase this way.
To help with this effort:
* Format all new code automatically (and beautifully!) with `clang-format`
* If you make a change to an existing file, we'll assume that you've broken anyone's branch who was using the file.
  Wait until your change has been merged, then immediately make a follow-up PR formatting the files you changed.
* If automatic formatting isn't feasible for some reason, try and match the existing style.

This approach allows reviewers to see the functional changes you made in diffs clearly, while also incrementally formatting code and not breaking others' branches excessively.
Ask the team for help if you are struggling with `clang-format`.

## PR Checklist
Authors and reviewers, try and ensure the following.

Before merging a PR:
* CI passes with a clean build, free of warnings or test failures (read the build log!)
* Unit tests where reasonable for new functionality (bonus points for unit tests for existing functionality!)
* commit history is sane
* `clang-format`ted new files

After merging:
* Follow-up PR to `clang-format` existing files you changed.

## Testing and Benchmarking
TODO what's a reasonable set of problems to run Vampire on to check for introduced bugs?

---

Happy hacking! -- the Vampire team.

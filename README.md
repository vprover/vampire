![GitHub release (latest by date)](https://img.shields.io/github/v/release/vprover/vampire)

# Vampire
This is the main source repository of the [Vampire](https://vprover.github.io) project, an advanced tool for automated reasoning.
The following is for end-users of Vampire: new developers should read the [wiki](https://github.com/vprover/vampire/wiki) as well.

## Licensing
Please see LICENCE for usage restrictions.
Note that Vampire's source includes a vendored copy of [Minisat](http://minisat.se/) and optionally links to [Z3](https://github.com/Z3Prover/z3).
Such code is provided under their own licence.

## Issue Tracking
Please use GitHub's integrated issue tracker to file bug reports and make suggestions for future Vampire features.
Please provide as much information and detail as possible in either case.

## Download
A statically-linked build suitable for running on StarExec is provided with each release; this may well run on your system also.
If not, you will need to build Vampire from source, but this is not too onerous.

## Basic Usage
The basic usage of Vampire is to save your problem in [TPTP](https://tptp.org) format and run
```shellsession
$ vampire problem.p
```
which will run Vampire in its default mode with a 60 second time-limit.

However, consider running Vampire in _portfolio_ mode:
```shellsession
$ vampire --mode casc problem.p
```
which will try lots of different _strategies_.
This often performs better than the default mode.

If you think the problem is satisfiable then you can also run
```shellsession
$ vampire --mode casc_sat problem.p
```
which will use a set of strategies suited to satisfiable problems.

Note that all of these modes are really shortcuts for other combinations e.g. `--mode casc` is a shortcut for
```shellsession
$ vampire --mode portfolio --schedule casc -p tptp
```

## Advanced Usage
To see a full list of options, run
```shellsession
$ vampire --show_options on
```

## Source Build
Vampire is built with the help of [CMake](https://cmake.org).
CMake does not run any build commands directly: instead, it can generate a number of different [output formats](https://cmake.org/cmake/help/latest/manual/cmake-generators.7.html), such as UNIX Makefiles.
If you are completely new to CMake, there is a [tutorial](https://cmake.org/cmake/help/latest/guide/user-interaction/index.html) for end-users.

A typical build on a UNIX-like system might look like this:
```shellsession
# make a clean directory to build Vampire into
$ mkdir /tmp/build && cd /tmp/build

# Configure the build and generate files with CMake
$ cmake /path/to/vampire
-- The C compiler identification is GNU 9.3.0
-- The CXX compiler identification is GNU 9.3.0
-- Check for working C compiler: /usr/bin/cc
-- Check for working C compiler: /usr/bin/cc -- works
-- Detecting C compiler ABI info
-- Detecting C compiler ABI info - done
-- Detecting C compile features
-- Detecting C compile features - done
-- Check for working CXX compiler: /usr/bin/c++
-- Check for working CXX compiler: /usr/bin/c++ -- works
-- Detecting CXX compiler ABI info
-- Detecting CXX compiler ABI info - done
-- Detecting CXX compile features
-- Detecting CXX compile features - done
-- Setting build type to 'Release' as none was specified.
-- Found Z3 4.8.9.0
-- Setting binary name to 'vampire_z3_rel_master_4933'
-- Configuring done
-- Generating done
-- Build files have been written to: /tmp/build

# Build Vampire, in this case with make(1)
$ make
<snip>

# You now have a Vampire binary
$ ls bin/
vampire_z3_rel_master_4933
$
```

Windows can be tricky. We are working on improving the situation, but in the meantime you might wish to look at the [Cygwin wiki page](https://github.com/vprover/vampire/wiki/Cygwin), and [related](https://github.com/vprover/vampire/issues/462) [bug](https://github.com/vprover/vampire/issues/318) [reports](https://github.com/vprover/vampire/issues/282).

### Adding Z3
Vampire can optionally link to a fixed version of the external Z3 library.
If you wish to do this, [initialise the `z3` submodule](https://git-scm.com/book/en/v2/Git-Tools-Submodules#_cloning_submodules) in the Vampire source directory.
Then follow the Z3 [CMake instructions](https://github.com/Z3Prover/z3/blob/master/README-CMake.md) to build the Z3 libraries into Vampire's tree at `z3/build/`.
This is where Vampire's build system will look for Z3: if it finds it, it will automatically link to Z3.
A reasonable Z3 build might look like this:
```shellsession
# Build Z3 into vampire/z3/build
$ mkdir -p /path/to/vampire/z3/build && cd /path/to/vampire/z3/build

# Configure single-threaded build, no debug symbols
$ cmake .. -DZ3_SINGLE_THREADED=1 -DCMAKE_BUILD_TYPE=Release
<snip>

# Build Z3, in this case with make(1)
$ make
<snip>
```

### Build Configuration
* Vampire can be statically linked, with e.g. `cmake /path/to/vampire -DBUILD_SHARED_LIBS=0`
* To compile Vampire in debug mode, add `-DCMAKE_BUILD_TYPE=Debug` to the cmake call.
* You may find setting a CMake installation directory (e.g. with `cmake /path/to/vampire -DCMAKE_INSTALL_PREFIX=/opt/vampire`) helpful.

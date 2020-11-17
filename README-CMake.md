### General Setup ###

The general process is as follows:

    mkdir build
    cd build
    cmake -G "Unix Makefiles" ..
    make -j8

The name of the build directory is not relevant and you might need to choose a
different generator based on your preference / platform. You can consult
`cmake -h` to get a list of build tools supported by your current installation
of cmake.

## Compile Flags ##

All compile flags are added as additional arguments to cmake - for example
`cmake -DEXAMPLE=value -G "Unix Makefiles" ..`.

* Target directory: `-DCMAKE_INSTALL_PREFIX=/opt/vampire-devel`
  Select install target, also helpful when compiling z3 to avoid collisions with
  other installed versions.

* Static compilation: `-DBUILD_SHARED_LIBS=0`
  This option only prefers static libraries over shared libraries which can
  lead to a mixed binary. You can check the output of the linking which
  libraries were not linked in. Please be also aware that Mac OS X does not
  support completely statically linked libraries (see also Apple's
  [Technical Q&A](https://developer.apple.com/library/archive/qa/qa1118/_index.html)).

* Debug build: `-DCMAKE_BUILD_TYPE=Debug`

# Z3
We now fix a known version of Z3 via git submodule.
If you don't need Z3, do nothing: CMake will detect this and do the right thing.
If you need Z3, first `git submodule update --init` to pull the correct version of Z3, then build Z3 via its own CMake system into `z3/build`, which is where Vampire's CMake will find the necessary files.
CMake will then detect this build and do the right thing.
Finally, if you've used Z3 in the past but don't want it for this build, pass `-DCMAKE_DISABLE_FIND_PACKAGE_Z3=1` to disable automatically including Z3.

## Building Z3
Please refer to `README-CMake.md` for detailed instructions on how to build Z3 using cmake. Notable options are:
  * `-DZ3_BUILD_LIBZ3_SHARED=0`: static library (z3 up to version 4.8.7 needs `-DBUILD_LIBZ3_SHARED=0` instead)
  * `-DCMAKE_INSTALL_PREFIX=/opt/z3-devel`: installation path

## Other Features ##

* Verbose compilation: if you would like to disable the progress reports and see
  the makefile output, call `make VERBOSE=1`.

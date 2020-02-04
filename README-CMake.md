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

* Z3 Path: use `-DZ3_DIR=$(PATH)` this is the path to the Z3 CMake configuration.
  MS: for me an absolute path to `/.../z3/build` works, where `build` is my own cmake build directory under z3 (after a successful compile of z3 there).
  It is usually located in `$Z3_ROOT/lib64/cmake/z3` but only when Z3 was built using cmake.
  Currently, the binary distribution of Z3 does not include these files.
  
  Please refer to `README-CMake.md` for detailed instructions on how to build Z3 using
  cmake. Notable options are:
  * `-DBUILD_LIBZ3_SHARED=0`: static library
  * `-DCMAKE_INSTALL_PREFIX=/opt/z3-devel`: installation path

  MS: curently, there is an issue with static linking against z3 (the produced exectuable immediately segfaults):
https://github.com/Z3Prover/z3/issues/2457
https://stackoverflow.com/questions/35116327/when-g-static-link-pthread-cause-segmentation-fault-why
 For now, I am manually fixing the final gcc/linker call to include the whole lpthread as described on the stackoverflow post above. I.e.
 `-pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive` is needed at the end of the command.

## Other Features ##

* Verbose compilation: if you would like to disable the progress reports and see
  the makefile output, call `make VERBOSE=1`.

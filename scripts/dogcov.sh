#!/bin/bash

# If you run cmake with -DCMAKE_BUILD_TYPE=Debug option, make will produce a version of vampire compiled
# with the extra gcov stuff included. This will cause coverage information to be stored alongside the
# object files here.
#
# This script produces an html summary of the coverage information.
# Run from the (cmake) build directory.
#
# Original version by Giles

mkdir -p gcovdata
lcov -j $1 --directory . --capture --output-file vampire.info
mv vampire.info gcovdata
cd gcovdata
genhtml -j $1 vampire.info
open index.html &

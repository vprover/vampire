#!/bin/bash

# If you have gcov installed you can do make vampire_gcov to produce a version of vampire compiled
# with the extra gcov stuff included. This will cause coverage information to be stored alongside the
# object files here.
#
# This script produces an html summary of the coverage information. Run here.
#
# By Giles

mkdir -p gcovdata
lcov --directory ~/git/vampire/ --capture --output-file vampire.info
mv vampire.info gcovdata
cd gcovdata
genhtml vampire.info
open index.html &

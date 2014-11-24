#!/bin/bash
mkdir -p gcovdata
lcov --directory ~/git/vampire/ --capture --output-file vampire.info
mv vampire.info gcovdata
cd gcovdata
genhtml vampire.info
open index.html &

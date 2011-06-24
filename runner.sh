#!/bin/bash

EXECUTABLE=$1
PROB_SRC=$2
OUTPUT=$3
shift 3

trap '' 1
cat $PROB_SRC | xargs -n 1 $EXECUTABLE --time_limit 60 --mode spider $* --input_file >$OUTPUT 2>&1 &


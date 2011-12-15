#!/bin/bash

# usage:
# ./run_on_problems.sh <vampire_exec> <vampire_arguments> <problem files ...>
# vampire_arguments must be passed as one argument (put into quotation marks)

EXEC_FILE=$1
EXEC_ARGS="$2"
shift 2
for F in $*; do
        echo PRB $F
        $EXEC_FILE $EXEC_ARGS $F 2>&1
done

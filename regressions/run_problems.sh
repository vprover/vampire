#!/bin/bash

TEST_DIR=`dirname $0`
PRB_DIR="$TEST_DIR/problems"

VEXEC_DBG="$TEST_DIR/../vampire_dbg"
VEXEC_REL="$TEST_DIR/../vampire_rel"

PRB_SCRIPT="$TEST_DIR/run_problem.sh"

for F in $PRB_DIR/*; do
        if ! $PRB_SCRIPT $VEXEC_DBG $F; then
                echo "# test $F failed for vampire debug build"
                exit 1
        fi
        if ! $PRB_SCRIPT $VEXEC_REL $F; then
                echo "# test $F failed for vampire release build"
                exit 1
        fi
done

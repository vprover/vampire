#!/bin/bash

TEST_DIR=`dirname $0`
SCRIPTS_CMD="$TEST_DIR/run_scripts.sh"
PROBLEMS_CMD="$TEST_DIR/run_problems.sh"

if ! $SCRIPTS_CMD; then
        echo "# script tests failed"
        exit 1
fi

if ! $PROBLEMS_CMD; then
        echo "# problem tests failed"
        exit 1
fi


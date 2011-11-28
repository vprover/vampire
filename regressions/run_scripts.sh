#!/bin/bash

TEST_DIR=`dirname $0`
SCR_DIR="$TEST_DIR/scripts"

for F in $SCR_DIR/*; do
        if ! $F; then
                echo "# test $F failed"
                exit 1
        fi
done

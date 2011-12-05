#!/bin/bash


if [ "$1" == "-d" ]; then
VUTIL_CMD="./vutil epr_restoring_scanner"
shift 1
else
VUTIL_CMD="./vutil_rel epr_restoring_scanner"
fi

for F in $*; do
        $VUTIL_CMD $F
done
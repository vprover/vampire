#!/bin/bash

VUTIL_CMD="./vutil epr_restoring_scanner"

for F in $*; do
        $VUTIL_CMD $F
done
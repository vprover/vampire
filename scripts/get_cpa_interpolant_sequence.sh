#!/bin/bash

#usage:
# get_cpa_interpolant_sequence.sh <vutil executable> <z3 executable> <cpa files>...
# 

VUTIL_EXEC=$1
Z3_EXEC=$2
shift 2

Z3_CMD="$Z3_EXEC PROOF_MODE=2 -smt2"

AUX_DIR=`mktemp -d -t ep_XXXXXX`
PRB_FILE="$AUX_DIR/prb.smt2"
Z3_OUT="$AUX_DIR/z3_out.txt"
PROOF_FILE="$AUX_DIR/proof.txt"

$VUTIL_EXEC sc $* | fold -w 200 -s >$PRB_FILE
$Z3_CMD $PRB_FILE >$Z3_OUT 2>&1

if ! grep -q "^unsat" $Z3_OUT; then
        echo "unsuccessful z3 run:"
        cat $Z3_OUT
        echo "========"
        rm -r $AUX_DIR
        exit 1
fi

grep -v ^unsat $Z3_OUT >$PROOF_FILE

LEFT_CNTS="`eval echo {1..$(($#-1))}`"

for LEFT_CNT in $LEFT_CNTS; do
        cat $PROOF_FILE | $VUTIL_EXEC zie $LEFT_CNT $*
        echo "========"
done


rm -r $AUX_DIR


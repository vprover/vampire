#!/bin/bash

#usage:
# get_cpa_interpolant_sequence.sh <vutil executable> <z3 executable> <cpa files>...
# 

#this is usable only for vampire
TIME_LIMIT=60
if [ "$1" == "-t" ]; then
        TIME_LIMIT=$2
        shift 2
fi



function run_vampire()
{
#        local VAMP_ARGS="-ptb off -aig_bdd_sweeping on -flatten_top_level_conjunctions on -aig_definition_introduction on -proof off -statistics none $TIME_LIMIT_SPEC"
        local VAMP_ARGS="-proof off -sio off -sac on -predicate_definition_inlining non_growing -statistics none -smtlib_flet_as_definition on -t $TIME_LIMIT"
        local LEFT_CNTS="`eval echo {1..$(($#-1))}`"
        
        for LEFT_CNT in $LEFT_CNTS; do
                echo "results for $BASE $LEFT_CNT"
#                $VUTIL_EXEC cpa $# $LEFT_CNT $* $VAMP_ARGS
                (ulimit -St $TIME_LIMIT; $VUTIL_EXEC cpa $# $LEFT_CNT $* $VAMP_ARGS) | grep -v "Refutation found"
                if [ $? -eq 130 ]; then
                        echo interrupted
                        exit 130
                fi
                echo "========"
        done
}


VUTIL_EXEC=$1
Z3_EXEC=$2
shift 2

BASE="`echo $1 | sed 's/-formula...\.smt$//'`"

if [ "$Z3_EXEC" == "-" ]; then
        run_vampire $*
        exit 0
fi

Z3_CMD="$Z3_EXEC PROOF_MODE=2 -smt2"

AUX_DIR=`mktemp -d -t ep_XXXXXX`
PRB_FILE="$AUX_DIR/prb.smt2"
Z3_OUT="$AUX_DIR/z3_out.txt"
PROOF_FILE="$AUX_DIR/proof.txt"

(ulimit -St $TIME_LIMIT; $VUTIL_EXEC sc $* ) | fold -w 200 -s >$PRB_FILE

if grep -q "^User error:" $PRB_FILE; then
        exit 0
fi

(ulimit -St $TIME_LIMIT; $Z3_CMD $PRB_FILE) >$Z3_OUT 2>&1

if grep -q "^sat$" $Z3_OUT; then
        exit 0
fi

if ! grep -q "^unsat" $Z3_OUT; then
        echo "on $BASE"
        echo "unsuccessful z3 run:"
        cat $Z3_OUT
        echo "========"
        rm -r $AUX_DIR
        exit 1
fi


grep -v ^unsat $Z3_OUT >$PROOF_FILE

LEFT_CNTS="`eval echo {1..$(($#-1))}`"

for LEFT_CNT in $LEFT_CNTS; do
        echo "results for $BASE $LEFT_CNT"
        cat $PROOF_FILE | (ulimit -St $TIME_LIMIT; $VUTIL_EXEC zie -b -q $LEFT_CNT $* )
        echo "========"
done

rm -r $AUX_DIR


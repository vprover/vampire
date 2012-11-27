#!/bin/bash

# Compares Vampire's solutions of given problems with and without 
# particular preprocessing enabled.
# Usage:
# eval_preprocessing.sh <vampire executable> <time> <file with problem file names, separated by white-space> <... arguments to compare with>

EXEC=$1
SOLVER_TIME=$2
PROBS_FILE=$3
shift 3
PARAMS=$*

OUTF=`mktemp -t ep_XXXXXX`

function eval_status() {
        #params <file> <... args>
        local F=$1
        shift 1
        $EXEC --mode casc -t $SOLVER_TIME $F $*>$OUTF
        local STATUS=`grep "SZS status" $OUTF | sed 's/^\% SZS status \([^ ]*\) for .*$/\1/'`
        local TOTAL_TIME=`grep "Success in time" $OUTF | sed 's/^\% Success in time \([^ ]*\) s$/\1/'`
        echo -n " $STATUS $TOTAL_TIME"
}


for F in `cat $PROBS_FILE` ; do
        echo -n $F
        eval_status $F
        eval_status $F $PARAMS
        echo
done

rm $OUTF

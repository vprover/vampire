#!/bin/bash

#usage:
# get_cpa_interpolants.sh <vutil executable> <z3 executable> <cpa directories>...
# 

SELF_DIR=`dirname $0`

VUTIL_EXEC=$1
Z3_EXEC=$2
shift 2

for DIR in $*; do
        for BASE in $DIR/interpolation????-formula000.smt ; do
                PATTERN="`echo $BASE|sed 's/formula000.smt/formula???.smt/'`"
                FILES="`eval echo $PATTERN`"
                $SELF_DIR/get_cpa_interpolant_sequence.sh $VUTIL_EXEC $Z3_EXEC $FILES
        done
done
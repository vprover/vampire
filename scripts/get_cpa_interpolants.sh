#!/bin/bash

#usage:
# get_cpa_interpolants.sh <vutil executable> <z3 executable> <cpa directories>...
# 

SELF_DIR=`dirname $0`

TIME_LIMIT_SPEC=""
if [ "$1" == "-t" ]; then
        TIME_LIMIT_SPEC="$1 $2"
        shift 2
fi


VUTIL_EXEC=$1
Z3_EXEC=$2
shift 2

for DIR in $*; do
        for BASE in $DIR/interpolation????-formula000.smt ; do
                if [ -a $BASE ]; then
                        PATTERN="`echo $BASE|sed 's/formula000.smt/formula???.smt/'`"
                        FILES="`eval echo $PATTERN`"
                        $SELF_DIR/get_cpa_interpolant_sequence.sh $TIME_LIMIT_SPEC $VUTIL_EXEC $Z3_EXEC $FILES
                        if [ $? -eq 130 ]; then
                                echo subprocess interrupted
                                exit 0
                        fi
                fi
        done
done
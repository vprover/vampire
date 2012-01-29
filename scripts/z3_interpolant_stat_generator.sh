#!/bin/bash

trap '' 1

TIME_LIMIT=120

VUTIL_EXEC=$1
shift 1

if [ "$1" == "-d" ]; then
        shift 1
        ARG=""
        if [ "$1" == "-r" ]; then
                ARG="-r"
                shift 1
        fi
        for DIR in $*; do
                $0 $VUTIL_EXEC $ARG $DIR/*
                if [ $? -eq 130 ]; then
                        echo interrupted
                        exit 130
                fi
        done
        exit 0
fi

FILES=$*

if [ "$1" == "-r" ]; then
        FILES=`echo $FILES |tr ' ' '\n'|sort -R`
fi

echo "============#"
for F in $FILES; do
        echo "F: $F"
        echo "Rq:"
        (ulimit -St $TIME_LIMIT; $VUTIL_EXEC zie -t $TIME_LIMIT -q < $F)
        RES_CODE=$?
        if [ $RES_CODE -eq 130 ]; then
                echo interrupted
                exit 130
        fi
        if [ $RES_CODE -ne 0 ]; then
                echo "error result code"
        fi

        echo "------#"

        echo "Bq:"
        (ulimit -St $TIME_LIMIT; $VUTIL_EXEC zie -b -t $TIME_LIMIT -q < $F)
        RES_CODE=$?
        if [ "$RES_CODE" -eq 130 ]; then
                echo interrupted
                exit 130
        fi
        if [ "$RES_CODE" -ne 0 ]; then
                echo "error result code"
        fi
        
        echo "============#"
done
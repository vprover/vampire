#!/bin/bash

#
#Script checks that only declared tracing tags are used in TRACE and LOG macros
#
#The check is not sound or complete, but works on the current use scenarios of 
#tracing macros. When there is a case in the code that gives wrong result, the 
#script should be updated to handle it.
#

LOG_MACROS="LOG|TRACE|LOGV|LOG_UNIT|LOG_INT"

SELF_DIR=`dirname $0`
SRC_DIR="$SELF_DIR/../.."

SRC_FILES="$SRC_DIR/*pp `find $SRC_DIR/[A-Z]* -name '*pp'`"

LOG_DECL_FILE="$SRC_DIR/Debug/Log_TagDecls.cpp"

ALLOWED_FILE=`mktemp -t eoa_allowed_XXXXX`
USED_FILE=`mktemp -t eoa_used_XXXXX`

grep 'DECL(".*"' "$LOG_DECL_FILE" | sed 's/.*DECL("\([^"]*\)".*$/\1/' | sort >$ALLOWED_FILE 

grep -h -v '^ *//' $SRC_FILES | egrep "($LOG_MACROS)"'[ ]*\("[^"]*"' | grep -v "^\s*//" | sed -E 's/^.*('"$LOG_MACROS"')[ ]*\("([^"]*)".*$/\2/' | sort -u >$USED_FILE

EXTRA=`join -v 2 $ALLOWED_FILE $USED_FILE`

rm $ALLOWED_FILE
rm $USED_FILE

if [ "$EXTRA" != "" ]; then
        echo "Undeclared trace tags:"
        echo "$EXTRA"
        exit 1
fi

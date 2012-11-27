#!/bin/bash

#
# clausifies a file in the special intel fof BMC format
#
#usage:
# cat file.fof | ./intel_clausify.sh {clausifier exec} {clausifier args...}

EXEC=$1
shift 1

PRB=`mktemp -t i2f_XXXXX`
PRB_CLEAN=`mktemp -t i2f_XXXXX`
PRB_CLAUSIFIED=`mktemp -t i2f_XXXXX`
PRB_DEFS=`mktemp -t i2f_XXXXX`

grep -v '^ *\(%.*\)\?$' >$PRB
grep '^tff(.*).' $PRB >$PRB_DEFS

cat $PRB | sed 's/^\(tff([^|]*\)|.*).$/\1 )./' | sed 's/\$\$/aaa__/g' >$PRB_CLEAN

$EXEC --protected_prefix aaa__ $PRB_CLEAN $* | sed 's/aaa__/$$/g' >$PRB_CLAUSIFIED

cat $PRB_DEFS $PRB_CLAUSIFIED

rm $PRB
rm $PRB_CLEAN
rm $PRB_CLAUSIFIED
rm $PRB_DEFS
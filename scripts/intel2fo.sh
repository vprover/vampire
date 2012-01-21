#!/bin/bash

#usage:
# cat file.fof | ./intel2fo.sh | ...

PRB=`mktemp -t i2f_XXXXX`
tr -d '\r' | grep -v '^ *\(%.*\)\?$' | grep -v '^ *$' >$PRB
cat $PRB | sed 's/^\(tff([^|]*\)|.*).$/\1 )./' | sed 's/\$\$equality_sorted([^,]*,\([^,]*\),\([^)]*\))/\1=\2/g' | sed 's/\$\$/aaa__/g'

rm $PRB
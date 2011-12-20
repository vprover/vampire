#!/bin/bash

#usage:
# cat file.fof | ./intel2fo.sh | ...

PRB=`mktemp -t i2f_XXXXX`
grep -v '^ *\(%.*\)\?$' >$PRB
cat $PRB | sed 's/^\(tff([^|]*\)|.*).$/\1 )./' | sed 's/\$\$/aaa__/g'

rm $PRB
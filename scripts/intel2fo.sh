#!/bin/bash

#
#transforms file in the special intel FO BMC format to the usual TPTP
#
#usage:
# cat file.fof | ./intel2fo.sh | ...

tr -d '\r' | grep -v '^ *\(%.*\)\?$' | grep -v '^ *$' | sed 's/^\(tff([^,]*, *type *,[^|]*\)|.*).$/\1 )./' | sed 's/\$\$equality_sorted([^,]*,\([^,]*\),\([^)]*\))/\1=\2/g' | sed 's/\$\$/aaa__/g'


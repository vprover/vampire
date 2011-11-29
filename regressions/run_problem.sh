#!/bin/bash

if [ $# -ne 2 ]; then
echo "Invalid number of arguments"
cat <<EOF
Usage:
 run_problem.sh {vampire executable} {problem file}

Problem files may contain tags in format
 "% {tag name}: {tag value}"

Supported tags in problem files
 params -- arguments to be passed to the vampiree executable
 res -- either sat or unsat, asserts expected result

Meaning of exit statuses
 0 -- test passed OK
 1 -- test failed
 2 -- invalid format of problem file
 3 -- invalid usage
EOF
exit 3
fi

function get_unique_tag_value()
{
        #Arguments: {tag name} {target variable name}
        local TAG=$1
        local TGT=$2
        local PATTERN="^% $TAG: \(.*\)$"
        if [ `grep "$PATTERN" $PRB | wc -l` -gt 1 ]; then
                echo "Error in $PRB: Only one $TAG tag alowed"
                exit 2
        fi
        TGT=`grep "$PATTERN" $PRB | sed "s/$PATTERN/\1/"`
}

VEXEC=$1
PRB=$2

get_unique_tag_value params PARAMS

OUTF=`mktemp -t rpXXXXXX`

$VEXEC $PARAMS $PRB > $OUTF 2>&1
STATUS=$?

if [ "$STATUS" -gt 1 ]; then
        cat $OUTF
        echo
        echo "Vampire exitted with error status $STATUS on $PRB"
        exit 1
fi

get_unique_tag_value res RES
case "$RES" in
"") ;;
"sat")
        if [ ! grep "Satisfiable!" $OUTF ]; then
                cat $OUTF
                echo
                echo "Vampire did not show satisfiability on $PRB"
                exit 1
        fi
        ;;
"unsat")
        if [ ! grep "Refutation found. Thanks to Tanya!" $OUTF ]; then
                cat $OUTF
                echo
                echo "Vampire did not prove unsatisfiability on $PRB"
                exit 1
        fi
        ;;
*)
        echo "Error in $PRB: Unrecognized res tag value: $RES"
        ;;
esac
 

rm $OUTF 
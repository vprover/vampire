#!/bin/bash

#
# verifies whether a computed interpolant is really an interpolant
#
# usage:
# interpolant_verifier.sh problem_name.p
#

if [ "$1" == "" ]; then
	PROBLEM=`mktemp -t ivXXXXX`
	TEMPORARY=1
	cat >$PROBLEM
else
	PROBLEM=$1
	TEMPORARY=0
fi

VAMPIRE="./vampire"
INTERPOLANT=`$VAMPIRE -spl off -show_interpolant minimized $PROBLEM|grep "Interpolant"|sed 's/^[^:]*: //'`

if awk "
BEGIN { right=0 }
/vampire\(right_formula\)\./ { right=1 }
 { if(!right) print }
/vampire\(end_formula\)\./ { right=0 }
END { print \"fof(conj,conjecture, $INTERPOLANT).\" }
" $PROBLEM | $VAMPIRE | grep "Refutation found" >/dev/null; then
	echo -n #just a dummy line
else
	echo "'A => I' doesn't hold for $INTERPOLANT"
fi

if awk "
BEGIN { left=0 }
/vampire\(left_formula\)\./ { left=1 }
 { if(!left) print }
/vampire\(end_formula\)\./ { left=0 }
END { print \"fof(conj,axiom, $INTERPOLANT).\" }
" $PROBLEM | $VAMPIRE | grep "Refutation found" >/dev/null; then
	echo -n #just a dummy line
else
	echo "'I /\ B |= false' doesn't hold for $INTERPOLANT"
fi


if [ "$1" == "" ]; then
	rm -f $PROBLEM
fi

#" $PROBLEM; then
#" $PROBLEM | $VAMPIRE; then
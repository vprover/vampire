#!/bin/bash

VAMP="./vampire_rel"
VUTIL="./vutil_rel"
V_OPTS="-mode casc -forced_options spl=off:ptb=off:gsp=off -show_interpolant minimized -t 10"

make $VAMP>/dev/null
make $VUTIL>/dev/null


AUX=`mktemp -t giXXXXX`
COLPRB=`mktemp -t giXXXXX`

for F in $*; do
	if grep '% Status   : Satisfiable' $F >/dev/null; then
		continue
	fi
	if grep '% Status   : CounterSatisfiable' $F >/dev/null; then
		continue
	fi
	for MODE in problem_coloring conjecture_coloring axiom_coloring; do
		if $VUTIL $MODE $F > $COLPRB; then
			echo -n #just a dummy command (bash doesn't like empty blocks)
		else
			continue #the coloring wasn't successful, so we skip this instance
		fi
		(ulimit -St 20; $VAMP $V_OPTS $COLPRB) | grep '^[^.]*nterpolant.*:' >$AUX
		if grep Interpolant $AUX >/dev/null; then
			echo $F $MODE
			cat $AUX
			echo '--------'
		fi
	done
done

rm $COLPRB
rm $AUX

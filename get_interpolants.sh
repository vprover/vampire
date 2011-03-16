#!/bin/bash

V_OPTS="--mode casc -show_interpolant on -forced_options spl=off:ptb=off -t 2"

AUX=`mktemp -t gi`

for F in $*; do
	echo -n $F": "
	if cat $F| ./vutil problem_coloring |./vampire_rel $V_OPTS>$AUX; then
		grep "^Interpolant" $AUX|sed "s/^Interpolant: //"
	else
		echo "[time out]"
	fi
done

rm $AUX

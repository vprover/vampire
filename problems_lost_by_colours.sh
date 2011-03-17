#!/bin/bash

V_OPTS="--mode casc -forced_options spl=off:ptb=off -t 2"
V_OPTS_INT="$V_OPTS -show_interpolant on"

AUX=`mktemp -t giXXXXX`

for F in $*; do
	echo -n $F
	if cat $F| ./vampire_rel $V_OPTS >/dev/null; then
		true
	else
		echo " not proved"
		continue
	fi
	
	if cat $F| ./vutil problem_coloring |./vampire_rel $V_OPTS_INT>$AUX; then
		echo " proved with colors"
		true
	else
		if grep "^Inferences skipped due to colors" $AUX >/dev/null; then
			echo -n " blocked: "
			grep "^Inferences skipped due to colors" $AUX|sed "s/^.*: //"|tr '\n' '%'|sed 's/%\(.\)/, \1/g'|tr -d '\n'|tr '%' '\n'
		fi
	fi
done

rm $AUX

#!/bin/bash

V_OPTS="--mode casc -forced_options spl=off:ptb=off -t 2"
V_OPTS_INT="$V_OPTS -show_interpolant on"
V_OPTS_UNB="$V_OPTS -show_interpolant on -color_unblocking on"

AUX=`mktemp -t giXXXXX`

for F in $*; do
	echo -n $F
	if cat $F| ./vampire_rel $V_OPTS >/dev/null; then
		true
	else
		if cat $F| ./vutil problem_coloring |./vampire_rel $V_OPTS_UNB>/dev/null; then
			echo " not proved, proved with colors and unblocking"
		else
			echo " not proved"
		fi
		continue
	fi
	
	if cat $F| ./vutil problem_coloring |./vampire_rel $V_OPTS_INT>$AUX; then
		echo " proved with colors"
	else
		if grep "^Inferences skipped due to colors" $AUX >/dev/null; then
			echo -n " blocked: "
			grep "^Inferences skipped due to colors" $AUX|sed "s/^.*: //"|tr '\n' '%'|sed 's/%\(.\)/, \1/g'|tr -d '\n%'
		fi
		if cat $F| ./vutil problem_coloring |./vampire_rel $V_OPTS_UNB>/dev/null; then
			echo -n " unblocking helped"
		fi
		echo
	fi
done

rm $AUX

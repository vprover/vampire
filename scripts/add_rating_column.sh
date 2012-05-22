#!/bin/bash

#add (at the end) a column with problem rating into a file where the first tab 
#separated column consists of tptp problem names


SCR_DIR=`dirname $0`
TPTP_PRB_DIR="$SCR_DIR/../Problems"

if [ "$1" == "-f" ]; then
	FULL=1
	shift
else
	FULL=0
fi

F=$1

cat $F | while read L
do
	if [ "$FULL" == "1" ]; then
		PRB=`echo $L | sed "s|^\([^[:space:]]*\) .*$|$TPTP_PRB_DIR/../\1|"`
	else
		PRB=`echo $L | sed "s|^\(...\)\([^[:space:]]*\).*|$TPTP_PRB_DIR/\1/\1\2.p|"`
	fi
   RTG=`grep '^. Rating' "$PRB" | sed 's/^. Rating   : \(.\...\).*$/\1/'`
   echo -e "$L\t$RTG"
done

#gawk '
#match($0, /(^[A-Z][A-Z][A-Z])([0-9][0-9][0-9][^\t]*)(\t|$)/, a) {
#        printf $0 "\t"
#        grCmd = "grep \"^% Rating\" /work/Dracula/Problems/" a[1] "/" a[1] a[2] ".p | sed \"s/^% Rating   : \\(.\\...\\).*$/\\1/\""
#        print " " |grCmd
#        close(grCmd)
#}
#
#' $F

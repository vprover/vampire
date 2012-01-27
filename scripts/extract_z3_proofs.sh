#!/bin/bash

TIME_LIMIT=120

if [ "$1" == "-d" ]; then
        DIR=$2
        OUT_DIR=$3
        for F in $DIR/*; do
                TGT=`echo $F | sed s^$DIR^$OUT_DIR^`.
                $0 $F $TGT || exit 1 
        done
        exit 0
fi 

Z3='./z3 -smt2'

AUX=`mktemp -d -t ezpXXXXX`

FILE=$1
OUT_PREFIX=$2
PRB=$AUX/prb.smt2
ZOUT=$AUX/zout

cat $FILE | sed "s/(check-sat)/(check-sat) (get-proof)/"> $PRB

#$Z3 PROOF_MODE=2 $PRB
ulimit -St $TIME_LIMIT
$Z3 PROOF_MODE=2 $PRB | awk -v "filePref=$OUT_PREFIX" '
{
        proofLine=1
}

BEGIN { fileIdx=1; outFile=filePref fileIdx; anythingOutput=0; haveFirstRes=0}
{ proofLine=1 }
/^success/ || /^sat/ || /^unsat/ || /^\(error/ {
        if(anythingOutput) {
                print "done with " outFile
                close(outFile)
                fileIdx+=1; outFile=filePref fileIdx; anythingOutput=0
        }
        proofLine=0
        haveFirstRes=1
}
proofLine==1 && haveFirstRes==1 {
        print > outFile
        anythingOutput=1
}

'

rm -r $AUX

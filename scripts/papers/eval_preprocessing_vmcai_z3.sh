#!/bin/bash

CL_EXEC=$1
shift
EXEC=$1
SOLVER_TIME=$2
PROBS_FILE=$3
shift 3
PARAMS=$*

OUTF=`mktemp -t ep_XXXXXX`
CLF=`mktemp -t ep_XXXXXX`

function eval_status() {
        #params <file> <... args>
        local F=$1
        shift 1
        (ulimit -St $SOLVER_TIME; $CL_EXEC --input_syntax smtlib --mode clausify $F $*) | grep -v "^tff" >$CLF
        time -p (ulimit -St $SOLVER_TIME; $EXEC -tptp $CLF)>$OUTF 2>&1 
                
        local STATUS=`grep "SZS status" $OUTF | sed 's/^\SZS status \([^ ]*\) for .*$/\1/'`
        local TOTAL_TIME=`grep "^real " $OUTF | sed 's/^real \(.*\)$/\1/'`
        echo -n " $STATUS $TOTAL_TIME"
}


for F in `cat $PROBS_FILE` ; do
        echo -n $F
        eval_status $F
        eval_status $F --aig_conditional_rewriting on
        eval_status $F --predicate_definition_merging on --flatten_top_level_conjunctions on --predicate_definition_inlining non_growing -aig_bdd_sweeping on -equality_propagation on -predicate_index_introduction on -aig_inliner on -predicate_equivalence_discovery definitions
        eval_status $F --predicate_definition_merging on --flatten_top_level_conjunctions on --predicate_definition_inlining non_growing -aig_bdd_sweeping on -equality_propagation on -predicate_index_introduction on -aig_inliner on -predicate_equivalence_discovery definitions -aig_conditional_rewriting on
        eval_status $F --predicate_definition_merging on --flatten_top_level_conjunctions on --predicate_definition_inlining non_growing -aig_bdd_sweeping on -equality_propagation on -predicate_index_introduction on -aig_inliner off -predicate_equivalence_discovery definitions -aig_conditional_rewriting on

        echo
done

rm $OUTF
rm $CLF
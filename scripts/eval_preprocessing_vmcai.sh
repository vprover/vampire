#!/bin/bash

# Compares Vampire's solutions of given problems with and without 
# particular preprocessing enabled.
# Usage:
# eval_preprocessing.sh <vampire executable> <time> <file with problem file names, separated by white-space> <... arguments to compare with>

EXEC=$1
SOLVER_TIME=$2
PROBS_FILE=$3
shift 3
PARAMS=$*

OUTF=`mktemp -t ep_XXXXXX`

function eval_status() {
        #params <file> <... args>
        local F=$1
        shift 1
        $EXEC --mode casc -t $SOLVER_TIME $F $*>$OUTF
        local STATUS=`grep "SZS status" $OUTF | sed 's/^\% SZS status \([^ ]*\) for .*$/\1/'`
        local TOTAL_TIME=`grep "Success in time" $OUTF | sed 's/^\% Success in time \([^ ]*\) s$/\1/'`
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

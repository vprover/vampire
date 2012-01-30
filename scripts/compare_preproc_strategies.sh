#!/bin/bash

if [ "$1" == "-d" ]; then
        VUTIL_EXEC=$2
        shift 2
        for DIR in $*; do
                $0 $VUTIL_EXEC $DIR/*
                if [ $? -eq 130 ]; then
                        echo interrupted
                        exit 130
                fi
        done
        exit 0
fi

TIME_LIMIT=10

 S[0]="-updr off -smtlib_introduce_aig_names off -inequality_splitting 0"
 S[1]="-inequality_splitting 0"
 S[2]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction off -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on -predicate_equivalence_discovery on -predicate_equivalence_discovery_all_atoms on -predicate_equivalence_discovery_sat_conflict_limit 10"
 S[3]="-smtlib_flet_as_definition off -smtlib_introduce_aig_names on -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -trivial_predicate_removal on -predicate_equivalence_discovery on -predicate_equivalence_discovery_all_atoms on -predicate_equivalence_discovery_sat_conflict_limit 10"
 S[4]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on -predicate_equivalence_discovery on -predicate_equivalence_discovery_all_atoms on -predicate_equivalence_discovery_sat_conflict_limit 50"
 S[5]="-smtlib_introduce_aig_names on -flatten_top_level_conjunctions on -inequality_splitting 0"
 S[6]="-smtlib_flet_as_definition off -smtlib_introduce_aig_names on -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0"
 S[7]="-smtlib_flet_as_definition on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining on -aig_bdd_sweeping on -inequality_splitting 0"
 S[8]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on"
 S[9]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction off -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on"
S[10]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on"
S[11]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on -predicate_equivalence_discovery on -predicate_equivalence_discovery_all_atoms on"
S[12]="-equality_propagation on -predicate_index_introduction on -smtlib_flet_as_definition on -predicate_definition_merging on -aig_definition_introduction on -smtlib_introduce_aig_names off -flatten_top_level_conjunctions on -predicate_definition_inlining non_growing -aig_bdd_sweeping on -inequality_splitting 0 -aig_inliner on -trivial_predicate_removal on -predicate_equivalence_discovery on -predicate_equivalence_discovery_all_atoms on -predicate_equivalence_discovery_sat_conflict_limit 10"

STRAT_IDXS="`eval echo {0..12}`"

TMP_OUT=`mktemp -t ep_XXXXXX`

function eval_strategy()
{
        if ! (ulimit -St $TIME_LIMIT; $VUTIL_EXEC pe -input_syntax smtlib $* >$TMP_OUT); then
                if [ $? -eq 130 ]; then
                        echo interrupted
                        exit 130
                fi
                if ! grep -q "SIGXCPU" $TMP_OUT; then 
                        cat $TMP_OUT 1>&2;
                else
                        echo -ne "TO\tTO\tTO\tTO\tTO"
                fi
        else
                cat $TMP_OUT
        fi
}


function eval_problem()
{
        local PRB=$1
        shift 1
        echo -ne "$PRB\t"
        for SI in $STRAT_IDXS; do
                eval_strategy $PRB ${S[$SI]}
                echo -ne "\t"
        done
        echo
}




VUTIL_EXEC=$1
shift 1

for F in $*; do
        eval_problem $F
done


rm $TMP_OUT
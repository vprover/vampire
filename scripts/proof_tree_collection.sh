
# The SMO division of CASC has too few test problems.  Generating
# problems by hand is very hard and time-consuming.  I was thinking about
# how test problems might be automatically generated.  I tried an idea of
# writing a theorem prover that would select a random literal from a
# knowledge base and attempt to prove it.  As it builds the search tree,
# it would keep track of how long all the paths are that it has tried.
# Once a path reaches a (possibly randomly generated) length, the "head"
# would get instantiated with randomly generated symbols.  In this way,
# we could generate as many test problems as desired.  By adding other
# tests, or preferences, we could vary the characteristics of the
# generated proofs, say by preferring (or not preferring) paths with
# equalities, or paths with big axioms.  We could generate lopsided proof
# trees by having big variation in the tree length test etc.

VAMPIRE_EXEC="./vampire"
VAMPIRE_PRINTING_OPTS="-show_preprocessing_formulas on -show_new on"
VAMPIRE_DEFAULT_OPTS="-propositional_to_bdd off -splitting off -general_splitting off -equality_proxy off -inequality_splitting 0 -naming 0 -forward_literal_rewriting on -global_subsumption on -unit_resulting_resolution on -saturation_algorithm discount -t 5"


AUX=`mktemp -d -t ezpXXXXX`

AUX_CLAUSES=$AUX"/clauses"

$VAMPIRE_EXEC $VAMPIRE_PRINTING_OPTS $VAMPIRE_DEFAULT_OPTS $* >$AUX_CLAUSES

#AUX_NON_INP=$AUX"/non_inp"
AUX_TREE_NODES=$AUX"/tree_nodes"
AUX_TN_REGEX=$AUX"/tn_regex"


grep -v '\[[^0-9]*]' $AUX_CLAUSES |grep '^New: '|sed 's/^New: \([0-9]*\)\. .* \([0-9,]*\)]$/\1 \2/'|tr ',' ' ' | awk '
BEGIN { maxWeight = 0; maxWeightCl = "" }

{
        cl = $1
        curWeight = 1
        curAncestors = ""
        for(i=2; i<=NF; i++) {
                par = $i
                if(treeWeight[par]) {
                        curWeight += treeWeight[par]
                }
                else {
                        curWeight += 1
                }
                if(ancestors[par]) {
                        curAncestors = curAncestors " " par ancestors[par]
                }
                else {
                        curAncestors = curAncestors " " par
                }
                
        }
        treeWeight[cl] = curWeight
        ancestors[cl] = curAncestors
        if(curWeight>maxWeight) {
                maxWeight = curWeight
                maxWeightCl = cl
        }
}

END {
        if(curWeight) {
                print cl ancestors[cl]
        }
}
' >$AUX_TREE_NODES

cat $AUX_TREE_NODES | sed 's/ /)|(/g' | sed 's/^\(.*\)$/New: ((\1))\\. /' >$AUX_TN_REGEX

egrep "`cat $AUX_TN_REGEX`" $AUX_CLAUSES

rm -r $AUX

% $distinct in what the model is checked against.
%
% The parser turns $distinct(a,b,c,d) into a marker literal over a "$distinct" predicate
% (Signature::getDistinctPredicate), and preprocessing expands it into disequalities, which FMB
% always does in full. The FMB self-check, however, reads the parsed input, marker and all,
% and evaluated the marker as an ordinary predicate the model knew nothing about: a correct
% model "FAILED" on $distinct(a,b,c,d). It is now evaluated as pairwise distinctness of its
% arguments, also under a negation (not_all_distinct), and the marker is not printed as a
% symbol of the model.

tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(c_type,type,c: $i).
tff(d_type,type,d: $i).
tff(e_type,type,e: $i).
tff(p_type,type,p: $i > $o).

tff(abcd,axiom, $distinct(a,b,c,d) ).
tff(not_all_distinct,axiom, ~ $distinct(a,b,c,d,e) ).
tff(p_a,axiom, p(a) & ~ p(b) ).

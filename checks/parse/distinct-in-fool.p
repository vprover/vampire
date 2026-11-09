% A $distinct marker can hide inside a FOOL term, where the formula walk has to
% descend to find it. If it escapes, it reaches the clause set as a free predicate
% and the distinctness is silently lost: a = b would no longer force the $ite to
% take its else branch. Must hold on both clausification pathways.

tff(c1_decl,type,
    c1: $i ).

tff(c2_decl,type,
    c2: $i ).

tff(p_decl,type,
    p: $i > $o ).

tff(ax,axiom,
    p($ite($distinct(a,b,c,d,e,f),c1,c2)) ).

tff(ax_eq,axiom,
    a = b ).

tff(c,conjecture,
    p(c2) ).

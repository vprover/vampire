% Unlike hol1.p, this one contains a lambda, so preprocessing sees an unshared
% literal carrying a SpecialFunctor::LAMBDA term. That is the shape that used to
% reach DistinctGroupExpansion's FOOL descent and abort with NOT_IMPLEMENTED.

thf(p_type, type, p: ( $i > $o ) > $o ).
thf(q_type, type, q: $i > $o ).

thf(ax, axiom,
    ( p @ ( ^ [X: $i] : ( q @ X ) ) ) ).

thf(thm, conjecture,
    ? [F: $i > $o] : ( p @ F ) ).

% The good old case: a $distinct asserted at a positive top level does hold
% unconditionally, so it becomes a distinct group. Must stay provable whether the
% group is expanded into disequalities or survives for DistinctEqualitySimplifier.

fof(ax, axiom,
    $distinct(a,b,c,d,e,f) ).

fof(c, conjecture,
    a != b ).

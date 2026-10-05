% A distinct group with a single member says nothing: it must not be left behind
% by DistinctGroupExpansion, or hasDistinctGroups() keeps reporting true and the
% strategy is needlessly incomplete (Options::complete). Satisfiable, not GaveUp.

fof(a, axiom,
    p("x") ).

fof(b, axiom,
    q(c) ).

% A $distinct under a disjunction is conditional, so a != b does not follow.
% The parser used to register the group regardless of context and prove it.

fof(ax, axiom,
    p | $distinct(a,b,c,d,e,f) ).

fof(c, conjecture,
    a != b ).

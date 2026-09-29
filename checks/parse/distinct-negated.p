% A negated $distinct says "not all of these are different", which is satisfiable.
% Both sizes matter: the parser used to expand fewer than five arguments in place
% (correct) but to register a distinct group for five or more, asserting the
% distinctness unconditionally and reporting this Unsatisfiable.

fof(small, axiom,
    ~ $distinct(a,b,c,d) ).

fof(large, axiom,
    ~ $distinct(p,q,r,s,t,u) ).

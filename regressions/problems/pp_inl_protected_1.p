% params: -mode clausify -updr on -predicate_definition_inlining non_growing --protected_prefix aa

% we want the result to be non-empty (if inlining of protected 
% predicates is done, all formulas would be eliminated) 

% grep: cnf


fof(ax1, axiom, aap(X) <=> p(X,a) ).
fof(ax1, axiom, aap(X) <=> aar(X) ).
fof(ax1, axiom, aap(b)).
fof(ax1, axiom, aar(c)).



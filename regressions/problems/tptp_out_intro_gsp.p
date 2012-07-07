% params: --proof tptp --general_splitting input_only
% res: unsat
% grep: new_symbols(naming,\[sP0\])

fof(a,axiom, ![X,Y]: ~p(X) | ~p(Y)).
fof(a,axiom, p(a)).
fof(a,axiom, p(b)).

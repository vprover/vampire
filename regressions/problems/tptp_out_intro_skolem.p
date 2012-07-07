% params: --proof tptp
% res: unsat
% grep: new_symbols(skolem,\[sK0\])

fof(a,axiom, ?[X]: p(X)).
fof(a,axiom, ![X]: ~p(X)).

% params: --proof tptp -ptb off -splitting backtracking
% res: unsat
% grep: new_symbols(naming,\[\$spl1\])

fof(a,axiom, p(a) | p(b)).
fof(a,axiom, ~p(a)).
fof(a,axiom, ~p(b)).

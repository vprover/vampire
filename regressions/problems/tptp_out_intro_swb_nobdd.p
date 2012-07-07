% params: --proof tptp -ptb off -splitting nobacktracking
% res: unsat
% grep: new_symbols(naming,\[sP0\])

fof(a,axiom, p(a) | p(b)).
fof(a,axiom, ~p(a)).
fof(a,axiom, ~p(b)).

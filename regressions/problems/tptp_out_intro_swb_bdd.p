% params: --proof tptp -ptb on -splitting nobacktracking
% res: unsat
% grep: new_symbols(naming,\[\$bdd1\])

fof(a,axiom, p(a) | p(b)).
fof(a,axiom, ~p(a)).
fof(a,axiom, ~p(b)).

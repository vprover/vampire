% params: --proof tptp -nm 4 -ptb off -updr off
% res: unsat
% grep: new_symbols(naming,\[sP0\])

fof(a,axiom, (a & b) | (c & d) | (e & f) ).
cnf(a,axiom, ~a).
cnf(a,axiom, ~c).
cnf(a,axiom, ~e).

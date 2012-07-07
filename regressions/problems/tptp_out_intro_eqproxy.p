% params: --equality_proxy RST --proof tptp -fde none
% res: unsat
% grep: new_symbols(naming,\[sQ0_eqProxy\])

fof(a,axiom, a=b).
fof(a,axiom, b=c).
fof(a,axiom, a!=c).

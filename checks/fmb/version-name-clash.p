% fmb/stale-definition.p with two input symbols in the way of the name its earlier version of
% x would get: 'x_$1' and 'x__$1' are taken, so the separator grows once more and the version
% is printed as 'x___$1'.

fof(def_x, axiom, ! [X] : ( x(X) <=> ( r(X) & s(X) ) )).
fof(u1, axiom, x(a)).
fof(u2, axiom, x(c)).
fof(u3, axiom, x(d)).
fof(o1, axiom, ~ r(b)).
fof(o2, axiom, ~ s(e)).
fof(clash, axiom, 'x_$1'(b) & ~ 'x__$1'(e)).

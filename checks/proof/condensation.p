% Full condensation instantiates both p(X) and q(X), creating a duplicate q(a).
cnf(main,axiom,p(X) | p(a) | q(X) | q(a)).
cnf(no_p,axiom,~p(a)).
cnf(no_q,axiom,~q(a)).

% Fast condensation removes p(X); the remaining literals stay unchanged.
cnf(main,axiom,p(X) | p(a) | q(b)).
cnf(no_p,axiom,~p(a)).
cnf(no_q,axiom,~q(b)).

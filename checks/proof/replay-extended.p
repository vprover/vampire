% A small refutation used with different options to exercise replay rules.
cnf(main,axiom,~p(X) | ~q(f(X)) | r(X)).
cnf(p,axiom,p(a)).
cnf(q,axiom,q(f(a))).
cnf(r,axiom,~r(a)).

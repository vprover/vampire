% A conditional flip, printed by -fmbmp layered as what it is: a definition of the
% predicate over the version of it below the flip.
%
% Under -bce on, c1 is blocked on r(X,Y) (its only resolvent on r, with c2, is a tautology),
% so it is eliminated, and the model reconstruction undoes that by a flip: wherever c1 is
% false, i.e. s holds of both arguments and r does not, make r true. The model prints r as
% r(X0,X1) <=> ('r_$1'(X0,X1) | ~(~s(X1) | ~s(X0) | 'r_$1'(X0,X1))), 'r_$1' being r before
% the flip, a table. Before, r was spelled out as a table, and later as a $cond listing the
% tuples the flip changes -- which is what a flip needing a fixed point still is (see
% fmb/cond-flip-fixpoint.p).

cnf(c1, axiom, r(X,Y) | ~s(X) | ~s(Y)).
cnf(c2, axiom, ~r(X,Y) | s(X) | t(Y)).
cnf(c3, axiom, ~s(a) | t(a)).
cnf(c4, axiom, s(b)).
cnf(c5, axiom, r(a,b) | r(b,a)).
cnf(c6, axiom, ~t(b) | ~t(a)).

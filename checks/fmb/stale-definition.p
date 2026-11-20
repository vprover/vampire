% A definition that is stale by the time the model is printed: it reads a symbol that changes
% after it, so it must be printed over that symbol's earlier version, not its final one.
%
% Unused predicate definition removal sees x used only positively, so it keeps only
% x => (r & s) and records a flip of x, to be replayed at the end. Predicate elimination,
% which runs later in preprocessing, then eliminates r and s, whose definitions mention x,
% and x itself. Replayed backwards, the definitions of r and s come before x's flip and read
% x as it was before it. So -fmbmp layered prints them over 'x_$1' (x before its last
% update, itself a definition), and x, a flip on top, as a $cond over 'x_$1' too. Before
% versions existed, r and s were spelled out as tables.
%
% x has three positive uses so that eliminating it first would cost more clauses than it
% removes; otherwise predicate elimination takes x before r and s, and nothing goes stale.

fof(def_x, axiom, ! [X] : ( x(X) <=> ( r(X) & s(X) ) )).
fof(u1, axiom, x(a)).
fof(u2, axiom, x(c)).
fof(u3, axiom, x(d)).
fof(o1, axiom, ~ r(b)).
fof(o2, axiom, ~ s(e)).

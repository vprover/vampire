% Parser regression test ('@' after a parenthesized formula as a connective
% argument): 'p & (q | r) @ x' has no legal THF reading; the leniency absorbs
% the application into the connective argument, 'p & ((q | r) @ x)', which is
% then rejected with a sort mismatch ((q | r) is of sort $o, not functional).
% This used to violate an assertion in higherPrecedence (also on master).
thf(dp, type, p: $o).
thf(dq, type, q: $o).
thf(dr, type, r: $o).
thf(dx, type, x: $o).
thf(a1, axiom, p & (q | r) @ x).

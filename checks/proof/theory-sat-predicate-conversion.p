% The learned EUF clause mixes predicate and equality literals, with both signs.
cnf(eq,axiom,a = b).
cnf(pos,axiom,p(a)).
cnf(neg,axiom,~p(b)).

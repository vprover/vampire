
cnf(ax2,axiom,
    c = d ).

cnf(ax2,axiom,
    f(f(c)) = c ).

cnf(ax3,axiom,
    e(f(c),f(c)) = f(c) ).

cnf(ax4,axiom,
    e(f(c),f(c)) = g(c,d) ).

cnf(ax3,axiom,
    f(g(X,Y)) = h(X,Y) ).

cnf(conj,negated_conjecture,
    h(X,X) != X ).

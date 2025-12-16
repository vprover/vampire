
cnf(ax1,axiom,
    c = d ).

cnf(ax2,axiom,
    g(d) = d ).

cnf(ax3,axiom,
    f(g(c),d) = d ).

cnf(conj,negated_conjecture,
    f(X,X) != X ).

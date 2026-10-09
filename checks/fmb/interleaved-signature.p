% Symbols of different kinds are deliberately declared in alternating order.
% Expected: Satisfiable, also with inferred sorts and monotonicity translations.
tff(a_type, type, a: $tType).
tff(c_type, type, c: a).
tff(p_type, type, p: a > $o).
tff(b_type, type, b: $tType).
tff(f_type, type, f: a > b).
tff(q_type, type, q: b > $o).
tff(d_type, type, d: b).
tff(g_type, type, g: b > a).
tff(ax1, axiom, p(c)).
tff(ax2, axiom, ![X:a]: (p(X) => q(f(X)))).
tff(ax3, axiom, ![Y:b]: g(Y) = c).
tff(ax4, axiom, f(c) != d).

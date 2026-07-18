% Parser regression test (unparenthesized THF applications): '@' binds tighter
% than connectives and binders, but the argument term used to be converted to
% a formula (or the binder closed) before the '@' was seen, giving confusing
% errors. This leniency is non-conforming and triggers a (once per run)
% warning. Expected: a1 = p & (f @ x); a2 = p & (g @ x @ y);
% a3 = heap = ^[T]: ((fb @ T) = e_b); exactly one warning.
thf(dp, type, p: $o).
thf(df, type, f: $o > $o).
thf(dg, type, g: $o > $o > $o).
thf(dx, type, x: $o).
thf(dy, type, y: $o).
thf(t1, type, tree_b: $tType).
thf(t2, type, e_b: tree_b).
thf(tf, type, fb: tree_b > tree_b).
thf(th, type, heap: tree_b > $o).
thf(a1, axiom, p & f @ x).
thf(a2, axiom, p & g @ x @ y).
thf(a3, axiom, heap = ( ^ [T: tree_b] : fb @ T = e_b ) ).

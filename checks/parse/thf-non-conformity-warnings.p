% Parser regression test (non-conformity warnings): each of the four kinds of
% leniently accepted non-conforming THF input below appears twice; each kind
% must be warned about exactly once per parser run.
thf(dp, type, p: $o).
thf(dq, type, q: $o).
thf(dr, type, r: $o).
thf(df, type, f: $o > $o).
thf(dx, type, x: $o).
thf(dg, type, g: $i > $i).
thf(a1, axiom, ~ p = q).
thf(a2, axiom, ~ q = p).
thf(b1, axiom, p & f @ x).
thf(b2, axiom, p | f @ x).
thf(c1, axiom, p = ~ q).
thf(c2, axiom, g = ^ [X: $i] : X).
thf(d1, axiom, p = q = r).
thf(d2, axiom, q = r = p).

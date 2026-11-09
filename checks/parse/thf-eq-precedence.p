% Parser regression test (THF equality binds tighter than binary connectives):
% the right-hand side of an equality used to be parsed greedily, reading a1 as
% p = (r & s) although the BNF mandates ((p) = r) & s.
% Expected: a1 = ((p) = r) & s; a2 = (p = q) <=> r; a3 keeps the application.
thf(dp, type, p: $o).
thf(dq, type, q: $o).
thf(dr, type, r: $o).
thf(ds, type, s: $o).
thf(df, type, f: $o > $o).
thf(dx, type, x: $o).
thf(a1, axiom, (p) = r & s).
thf(a2, axiom, p = q <=> r).
thf(a3, axiom, p = f @ x).

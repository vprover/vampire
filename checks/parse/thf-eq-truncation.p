% Parser regression test (THF equality after formula/application): a pending
% connective or application used to be dropped at '='/'!=' ("p &" resp. "f @"
% was silently lost). Expected: a1 reads as p & ((q) = r), a2 as (f @ x) = y.
thf(dp, type, p: $o).
thf(dq, type, q: $o).
thf(dr, type, r: $o).
thf(df, type, f: $o > $o).
thf(dx, type, x: $o).
thf(dy, type, y: $o).
thf(a1, axiom, p & (q) = r).
thf(a2, axiom, f @ x = y).

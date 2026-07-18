% Parser regression test (TFF/FOOL equality vs. connectives): a pending binary
% connective used to be dropped when '='/'!=' followed a parenthesized formula,
% silently truncating the input ("p &" resp. "& s" was lost).
% Expected: a1 reads as p & ((q) = r), a2 as ((p) = r) & s.
tff(dp, type, p: $o).
tff(dq, type, q: $o).
tff(dr, type, r: $o).
tff(ds, type, s: $o).
tff(a1, axiom, p & (q) = r).
tff(a2, axiom, (p) = r & s).

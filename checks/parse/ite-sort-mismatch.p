% Parser regression test ($ite sort checking): mismatched branch sorts must be
% reported with the dedicated message (and before the term is constructed).
% Expected: rejected with "sort mismatch in the if-then-else".
tff(dp, type, p: $o).
tff(a, axiom, $ite(p, 1, $true) = 2).

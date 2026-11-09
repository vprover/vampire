% Parser regression test (internal proxy names): vAND, vNOT, vPI, ... are
% Vampire's internal HOL proxy constants; outside THF mode they used to
% capture identically named user symbols, giving bizarre sort errors.
% Expected: all parse as ordinary user symbols.
fof(a1, axiom, p(vAND) & p(vNOT)).
tff(dv, type, vPI: $i > $i).
tff(dc, type, c: $i).
tff(a2, axiom, vPI(c) = c).

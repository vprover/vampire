% Parser regression test ($let parsing, incl. the by-reference scope lookups).
% Expected: parses with the binding f(X) := $sum(X, 1).
tff(a, axiom, $let(f: $int > $int, f(X) := $sum(X, 1), f(3)) = 4).

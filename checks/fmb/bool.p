% FMB over a problem that uses $o as an ordinary sort (the FOOL fragment consisting of
% $true and $false at term level). FOOLElimination compiles the booleans into ordinary
% terms and TheoryAxioms::applyFOOL pins their domain to two elements, so FMB models $o
% like any other sort; the model prints its two elements as $true and $false.
%
% f exercises $o as a result sort (the parser turns such a declaration into a predicate),
% g exercises it as an argument sort, and both keep it alive through preprocessing.

tff(t1, type, f: $i > $o).
tff(t2, type, g: ($o * $i) > $i).
tff(t3, type, a: $i).

tff(ax1, axiom, f(a) = $true).
tff(ax2, axiom, ?[Y:$i]: f(Y) = $false).
tff(ax3, axiom, ![B:$o, X:$i]: f(g(B,X)) = B).

% Parser regression test (conjectures filtered out by include() selection):
% the conjecture in the included file is not selected, so the problem must
% count as having no conjecture. Expected: SZS status Unsatisfiable
% (not ContradictoryAxioms, which the parser used to report).
include('include-selection-axioms.p', [27]).
fof(neg, axiom, ~twenty_seven).

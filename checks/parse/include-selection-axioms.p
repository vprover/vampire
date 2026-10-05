% Shared axiom file for the include() regression tests (include-selection.p,
% include-filtered-conjecture.p). Note the integer-named unit.
fof(27, axiom, twenty_seven).
fof(named, axiom, named_axiom).
fof(unselected, axiom, should_not_be_included).
fof(c, conjecture, filtered_conjecture).

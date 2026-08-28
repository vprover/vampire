% Parser regression test (block comments): a comment ending in '**/' never
% used to be closed, silently swallowing the rest of the file.
% Expected: both units are parsed.
fof(a1, axiom, first_unit_parsed). /* comment ending in a double star **/
fof(a2, axiom, second_unit_parsed).

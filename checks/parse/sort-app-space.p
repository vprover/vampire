% Parser regression test (whitespace in sort applications): 'list (A)' with a
% space used to fail with "Undeclared type constructor list/0" because the
% parser peeked at the raw character after the name.
% Expected: parses the same as list(A).
tff(t1, type, list: $tType > $tType).
tff(t2, type, nil: !>[A: $tType]: list (A)).

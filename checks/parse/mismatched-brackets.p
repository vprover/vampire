% Parser regression test (delimiter matching): 'p(a]' used to be accepted as
% if it were 'p(a)'. Expected: rejected with ") expected after an end of a term".
fof(a, axiom, p(a]).

% Regression: the ALASCA int->real conversion (-alascai) appends an integrality
% axiom floor(f(X)) = f(X) for every int-valued symbol it replaces. That clause
% has no premise, so it must not be built with a premise-carrying Inference kind.
%
% The conversion turns the two axioms below into
%   f'(c') != $floor(f'(c')) | $greater(f'(c'), 0)
%   f'(c') != $floor(f'(c')) | $less(f'(c'), 1)
% so the contradiction is reachable only via the integrality axioms.
tff(c_type, type, c: $int).
tff(f_type, type, f: $int > $int).
tff(a1, axiom, $greater(f(c), 0)).
tff(a2, axiom, $less(f(c), 1)).

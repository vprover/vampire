% Parser regression test: an equality at the *term* level did not resume connective
% parsing after itself, so a connective following it was an unexpected token,
% reported as ", ) or ] expected after an end of a term". "r(X = a & p(X))" (a1)
% failed at the '&' while "r(p(X) & X = a)" (a2), the same thing with the
% connective first, parsed. The term-level counterpart of the eq-precedence.p case.
%
% Expected: a1, a3 and a4 all read as r((X = a) & p(X)) -- a3 being the
% parenthesized spelling that used to be the only way to write it.
%
% a5 is what the guard is *for* and must not change: at the top level of an
% equality's right-hand side a connective still ends the term, so this reads as
% (d = X) & p(X) and not d = (X & p(X)).
tff(alpha_type, type, alpha: $tType).
tff(a_type, type, a: alpha).
tff(d_type, type, d: alpha).
tff(p_type, type, p: alpha > $o).
tff(r_type, type, r: $o > $o).

tff(a1, axiom, ! [X: alpha] : r(X = a & p(X))).
tff(a2, axiom, ! [X: alpha] : r(p(X) & X = a)).
tff(a3, axiom, ! [X: alpha] : r((X = a & p(X)))).
tff(a4, axiom, ! [X: alpha] : r(X = a & p(X))).
tff(a5, axiom, ! [X: alpha] : (d = X & p(X))).

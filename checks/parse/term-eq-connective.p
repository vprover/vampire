% Parser regression test: connectives and equality at the *term* level, i.e. inside
% a parenthesized argument list. Two defects used to make the '&' below an
% unexpected token, reported as ", ) or ] expected after an end of a term":
%
%   a1  an equality did not resume connective parsing after itself, so
%       "r(X = a & p(X))" failed while "r(p(X) & X = a)" (a2) parsed. The
%       term-level counterpart of the eq-precedence.p case.
%   a4  the equality-argument guard was never cleared on the way into a nested
%       argument list, so *any* connective there failed once the whole term sat to
%       the right of an '=': "d = h(p(X) & p(a))" failed, "h(p(X) & p(a))" alone
%       parsed. a5 is the two defects together.
%
% Expected: a1, a3 and a6 all read as r((X = a) & p(X)) -- a3 being the
% parenthesized spelling that used to be the only way to write it -- and a4, a5 as
% d = h(... & ...).
%
% a7 is what the guard is *for* and must not change: at the top level of an
% equality's right-hand side a connective still ends the term, so this reads as
% (d = X) & p(X) and not d = (X & p(X)).
tff(alpha_type, type, alpha: $tType).
tff(a_type, type, a: alpha).
tff(d_type, type, d: alpha).
tff(h_type, type, h: $o > alpha).
tff(p_type, type, p: alpha > $o).
tff(r_type, type, r: $o > $o).

tff(a1, axiom, ! [X: alpha] : r(X = a & p(X))).
tff(a2, axiom, ! [X: alpha] : r(p(X) & X = a)).
tff(a3, axiom, ! [X: alpha] : r((X = a & p(X)))).
tff(a4, axiom, ! [X: alpha] : d = h(p(X) & p(a))).
tff(a5, axiom, ! [X: alpha] : d = h(X = a & p(X))).
tff(a6, axiom, ! [X: alpha] : r(X = a & p(X))).
tff(a7, axiom, ! [X: alpha] : (d = X & p(X))).

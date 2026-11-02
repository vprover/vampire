% A compact exercise for FMB's model construction in the presence of
% preprocessing-eliminated symbols (cf. FiniteModelMultiSorted):
%
% - q is an unused predicate definition: default preprocessing (updr) eliminates it,
%   implicitly taking f along (f's only occurrence is in q's definition), so the model
%   must describe q symbolically (via the recorded definition) and f trivially;
%
% - t is non-monotonic (its domain is capped by positive variable equalities), so under
%   --fmb_adjust_sorts predicate/function FMB introduces sort predicates/functions whose
%   elimination from the finished model reencodes all symbol tables -- including the
%   unrepresented (empty) ones of q and f;
%
% - under -updr off -bce on, q's definition clauses are instead eliminated as blocked
%   clauses, and replaying the recorded conditional flips must first evaluate through
%   eliminated symbols and materialize q's table before flipping into it.
tff(s_type, type, s: $tType).
tff(t_type, type, t: $tType).
tff(c_type, type, c: s).
tff(d1_type, type, d1: t).
tff(d2_type, type, d2: t).
tff(f_type, type, f: s > s).
tff(p_type, type, p: s > $o).
tff(q_type, type, q: s > $o).
tff(r_type, type, r: t > $o).
tff(a1, axiom, p(c)).
tff(a2, axiom, ![X:s]: (q(X) <=> p(f(X)))).
tff(a3, axiom, ?[X:s]: ~p(X)).
tff(a5, axiom, ![Y:t]: (Y = d1 | Y = d2)).
tff(a6, axiom, r(d1) & ~r(d2)).

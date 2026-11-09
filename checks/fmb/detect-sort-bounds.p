% -fmbdsb builds injectivity/surjectivity claims for functions whose argument
% sorts differ from their result sort. For arity >= 2 the "padding" arguments
% get existentially quantified, and their sorts must come from the function
% type: deriving them from the claim formulas asks SortHelper for two different
% sorts for the same variable (injective binds 1 as a, surjective binds 1 as b)
% and trips the consistency check in SortHelper::collectVariableSorts.

tff(a_type, type, a: $tType).
tff(b_type, type, b: $tType).

tff(f_type, type, f: (a * b) > b).

tff(ca_type, type, ca: a).
tff(cb_type, type, cb: b).

tff(ax, axiom, f(ca,cb) = cb).

% Parser regression test (THF '~' vs '='): '~ p = q' is not legal THF; it used
% to be read as (~ p) = q, contradicting the reading FOF/TFF mandates for the
% same text. Expected: read as ~ (p = q), with a non-conformity warning.
thf(dp, type, p: $o).
thf(dq, type, q: $o).
thf(a, axiom, ~ p = q).

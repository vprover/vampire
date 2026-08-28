% Parser regression test (unparenthesized THF applications): '@' binds tighter
% than connectives, but the argument term used to be converted to a formula
% before the '@' was seen, giving confusing errors. This leniency is
% non-conforming and triggers a (once per run) warning. Binder bodies do NOT
% absorb a following '@' (see thf-lambda-in-app-chain.p).
% Expected: a1 = p & (f @ x); a2 = p & (g @ x @ y); exactly one warning.
thf(dp, type, p: $o).
thf(df, type, f: $o > $o).
thf(dg, type, g: $o > $o > $o).
thf(dx, type, x: $o).
thf(dy, type, y: $o).
thf(a1, axiom, p & f @ x).
thf(a2, axiom, p & g @ x @ y).

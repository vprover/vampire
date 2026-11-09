% Parser regression test (empty parentheses in THF): 'f @ ()' used to hit an
% assertion in debug builds and silently fabricate a negation proxy in release
% builds. Expected: rejected with "formula or term expected".
thf(df, type, f: ($o > $o) > $o).
thf(a, axiom, f @ ()).

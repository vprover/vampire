% Parser regression test (connective-as-term sections): (<~>) used to be a
% parse error although (&), (|), (=>), (<=>) worked.
% Expected: parses as an application of the xor proxy.
thf(dg, type, g: ($o > $o > $o) > $o).
thf(a, axiom, g @ (<~>)).

% Parser regression test (unsupported !> in formulas): must give a dedicated
% message, not a generic parse error. Expected: rejected with "only supports
% type quantification (!>) in type declarations".
thf(a, axiom, !> [A: $tType] : $true).

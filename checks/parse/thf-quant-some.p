% Parser regression test (unsupported ?*): must give a dedicated message, not
% a generic parse error. Expected: rejected with
% "cannot parse the ?* quantifier".
thf(a, axiom, ?* [X: $o] : X).

% A predicate whose table cannot be represented: blocked clause elimination removes both of
% big's clauses, so the model learns about it only from the recorded flips and has to
% materialize a table to carve them into -- but big has arity 40 over a two-element domain,
% i.e. 2^40 rows. That allocation is not one we can afford, and not one we could print
% either, so it must be refused up front: failing in the allocator instead is not reportable
% (the reporting wants memory of its own, and with overcommit the process is killed while the
% rows are written rather than getting an exception at all).
cnf(two_elements,axiom,
    a != b ).

cnf(big_needs_p,axiom,
    ( ~ big(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)
    | p(X0) ) ).

cnf(p_gives_big,axiom,
    ( ~ p(X0)
    | big(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) ) ).

cnf(p_holds_of_a,axiom,
    p(a) ).

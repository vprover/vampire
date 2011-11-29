% params: --epr_preserving_skolemization on
% res: sat

fof(axiom_8,axiom,
    q(X) <=> ? [Y0] : r(Y0) ).

fof(axiom_2,axiom,
    p(X) <=> ? [Y] : q(Y) ).

fof(axiom_10,axiom,
        p(a) ).
      
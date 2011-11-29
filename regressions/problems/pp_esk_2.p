% params: --epr_preserving_skolemization on
% res: sat

fof(axiom_42,axiom,
        p(X) <=> ? [Y] : q(Y) ).

fof(axiom_44,axiom,
    r(X) <=> ! [Y] : p(Y) ).

fof(axiom_49,axiom,
    ( r(a) )).



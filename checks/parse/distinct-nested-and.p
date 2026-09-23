% A $distinct reached through a top-level conjunction and a universal quantifier
% is still asserted unconditionally, so it should become a distinct group rather
% than be expanded.

fof(ax, axiom,
    ! [X] : ( $distinct(a,b,c,d,e,f) & ( p(X) | ~ p(X) ) ) ).

fof(c, conjecture,
    a != b ).

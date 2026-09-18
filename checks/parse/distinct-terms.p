% $distinct over compound terms: it cannot become a distinct group, whose members
% must be constants, so it is expanded into disequalities instead.

fof(ax, axiom,
    $distinct(f(x),b,c,d,e,g(y)) ).

fof(c, conjecture,
    f(x) != g(y) ).

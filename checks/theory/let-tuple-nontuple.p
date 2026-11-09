%----A monomorphic tuple binding whose right hand side is not a tuple
%----literal: the components are bound to projections out of a fresh
%----constant standing for the right hand side.
tff(g_type,type,g: [$int,$int]).
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, ! [X: $int, Y: $int] : ( [X,Y] != g | p(X,Y) ) ).
tff(c,conjecture, $let([a: $int, b: $int], [a,b] := g, p(a,b))).

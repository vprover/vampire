%----A tuple binding with a Boolean component whose right hand side is not
%----a tuple literal: the components are bound to projections out of the
%----right hand side, and projections are functions even for $o components.
tff(g_type,type,g: [$o,$int]).
tff(p_type,type,p: $int > $o).
tff(ax,axiom, ! [X: $o, Y: $int] : ( [X,Y] != g | ( X <=> p(Y) ) ) ).
tff(c,conjecture, $let([a: $o, b: $int], [a,b] := g, ( a <=> p(b) ) ) ).

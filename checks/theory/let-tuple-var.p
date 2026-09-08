%----A tuple binding whose right hand side is a variable bound outside.
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, ! [X: $int, Y: $int] : p(X,Y)).
tff(c,conjecture,
    ! [Z: [$int,$int]] : $let([a: $int, b: $int], [a,b] := Z, p(a,b))).

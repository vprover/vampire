%----Tuple bindings nested inside one another, and a tuple binding
%----standing next to an ordinary one in a simultaneous group.
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, ! [X: $int] : p(X,X)).
tff(c1,conjecture,
    $let([a: $int, b: $int], [a,b] := [1,2],
      $let([c: $int, d: $int], [c,d] := [b,a],
        ( p(a,d) & p(b,c) ) ) ) ).

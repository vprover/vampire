%----A tuple binding that is not the first definition of a simultaneous
%----definition group.
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, ! [X: $int] : p(X,X)).
tff(c,conjecture,
    $let([f: $int > $int, a: $int, b: $int],
         [f(X) := X, [a,b] := [1,1]],
         p(f(a),b) ) ).

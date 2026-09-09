%----A tuple binding in a simultaneous group with a function binding.
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, ! [X: $int] : p(X,X)).
tff(c,conjecture,
    $let([a: $int, b: $int, f: $int > $int],
         [[a,b] := [1,1], f(X) := X],
         p(f(a),b) ) ).

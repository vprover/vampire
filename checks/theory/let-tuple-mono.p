%----A monomorphic tuple binding with a tuple literal right hand side,
%----which is turned into a nest of single-symbol bindings.
tff(f_type,type,f: $int > $int).
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, p(f(1),2)).
tff(c,conjecture, $let([a: $int, b: $int], [a,b] := [f(1),2], p(a,b))).

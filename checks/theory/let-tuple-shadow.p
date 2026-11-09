%----The names bound by a tuple $let shadow global symbols only inside the
%----body; an occurrence in the right hand side still refers to the global.
tff(a_type,type,a: $int).
tff(b_type,type,b: $int).
tff(p_type,type,p: ($int * $int) > $o).
tff(ax,axiom, p(b,a)).
tff(c,conjecture, $let([a: $int, b: $int], [a,b] := [b,a], p(a,b))).

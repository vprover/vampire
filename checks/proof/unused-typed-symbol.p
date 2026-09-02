% expected: the proof stays fof even though p has a typed declaration.
tff(p_decl,type, p: $int > $o ).
fof(a1,axiom, q(a) ).
fof(c1,conjecture, q(a) ).

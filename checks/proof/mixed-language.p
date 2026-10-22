% expected: the whole proof is tff, with no fof lines after p's type
% declaration.
tff(p_decl,type, p: $int > $o ).
tff(erased,axiom, p(1) | $is_int(6) ).
fof(a1,axiom, q(a) ).
fof(c1,conjecture, q(a) ).

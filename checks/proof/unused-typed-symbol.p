% p is declared with a typed signature but never occurs in a formula, so the
% problem parses as untyped and the proof is fof. The declaration is printed
% from the signature, which used to put a tff line in front of the fof proof.
tff(p_decl,type, p: $int > $o ).
fof(a1,axiom, q(a) ).
fof(c1,conjecture, q(a) ).

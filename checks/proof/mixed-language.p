% p is the only symbol of a sort other than $i, and the only unit mentioning it
% collapses to $true during preprocessing. The signature keeps p, so its type
% declaration is still printed, while the surviving units are all $i. Choosing
% the proof output language from a Problem property therefore used to emit a tff
% type declaration followed by fof formulas in the same proof.
tff(p_decl,type, p: $int > $o ).
tff(erased,axiom, p(1) | $is_int(6) ).
fof(a1,axiom, q(a) ).
fof(c1,conjecture, q(a) ).

% the latest TPTP BNF allows $distinct in thf, always in functional form,
% but Vampire does not support it there

thf(a_decl,type,
    a: $i ).

thf(b_decl,type,
    b: $i ).

thf(c, axiom,
    $distinct(a,b) ).

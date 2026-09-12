% $distinct may only relate constants of one sort

tff(letter_type,type,
    letter: $tType ).

tff(a_decl,type,
    a: letter ).

tff(b_decl,type,
    b: $i ).

tff(ax,axiom,
    $distinct(a,b) ).

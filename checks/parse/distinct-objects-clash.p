% a distinct object used before being declared defaults to $i, so a later
% declaration at another sort is a clash

tff(letter_type,type,
    letter: $tType ).

tff(q_decl,type,
    q: $i > $o ).

tff(ax_use,axiom,
    q("a") ).

tff(a_decl,type,
    "a": letter ).

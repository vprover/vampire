% distinct objects (doubly-quoted symbols) may be declared at a user sort in tff;
% they are then pairwise distinct within that sort, independently of the $i ones

tff(letter_type,type,
    letter: $tType ).

tff(a_decl,type,
    "a": letter ).

tff(b_decl,type,
    "b": letter ).

tff(c_decl,type,
    "c": letter ).

tff(p_decl,type,
    p: letter > $o ).

tff(q_decl,type,
    q: $i > $o ).

% the $i-sorted distinct objects go to their own group
tff(ax_i,axiom,
    q("x") & q("y") ).

tff(ax_only_a,axiom,
    ! [X: letter] : ( p(X) => X = "a" ) ).

tff(ax_b,axiom,
    p("b") ).

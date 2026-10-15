% the fof behaviour of distinct objects is unchanged: they are $i-sorted and
% all of them live in one group

fof(ax_only_a,axiom,
    ! [X] : ( p(X) => X = "a" ) ).

fof(ax_b,axiom,
    p("b") ).

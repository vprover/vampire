% $distinct whose arguments have a non-ground sort cannot be given a monomorphic
% marker predicate, and could never become a distinct group either (its arguments
% are variables, not constants), so it is expanded at parse time instead.

tff(list_type,type,
    list: $tType > $tType ).

tff(nil_decl,type,
    nil: !>[X: $tType]: list(X) ).

tff(p_decl,type,
    p: !>[X: $tType]: ( list(X) > $o ) ).

tff(ax,axiom,
    ! [X: $tType, L: list(X)] : ( p(X,L) => $distinct(L,nil(X)) ) ).

tff(c,conjecture,
    ! [X: $tType, L: list(X)] : ( p(X,L) => L != nil(X) ) ).

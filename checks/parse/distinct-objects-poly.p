% a distinct object of a polymorphic (non-ground) sort is not supported

tff(list_type,type,
    list: $tType > $tType ).

tff(a_decl,type,
    "a": !>[X: $tType]: list(X) ).

tff(list_type, type-datatype, list : $tType > $tType).
tff(nil_type, type-datatype_constructor, nil : !>[A : $tType]: list(A)).
tff(cons_type, type-datatype_constructor, cons : !>[A : $tType]: ( A * list(A) ) > list(A)).

tff(cons_not_nil, conjecture,
    ![A : $tType, X : A, Y : list(A)]: cons(A,X,Y) != nil(A)).

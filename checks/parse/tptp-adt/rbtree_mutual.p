%----declare types first
tff(red_type,type-datatype,
    red: $tType > $tType ).

tff(black_type,type-datatype,
    black: $tType > $tType ).

%----types have been declared now, any order works
tff(rLeaf_type,type-datatype_constructor,
    rLeaf:
      !>[A: $tType] : ( A > red(A) ) ).

tff(bLeaf_type,type-datatype_constructor,
    bLeaf:
      !>[A: $tType] : ( A > black(A) ) ).

tff(rBranch_type,type-datatype_constructor,
    rBranch:
      !>[A: $tType] : ( ( black(A) * black(A) ) > red(A) ) ).

tff(bBranch_type,type-datatype_constructor,
    bBranch:
      !>[A: $tType] : ( ( red(A) * red(A) ) > black(A) ) ).

tff(rleaf_not_rbranch, conjecture,
    ![A : $tType, X : A, Y : black(A), Z : black(A)]: rLeaf(A,X) != rBranch(A,Y,Z)).

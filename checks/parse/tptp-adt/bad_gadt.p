tff(sum_type,type-datatype,
    sum: ( $tType * $tType ) > $tType ).

tff(inl_type,type-datatype_constructor,
    inl:
      !>[A: $tType,B: $tType] : ( B > sum(B,A) ) ).

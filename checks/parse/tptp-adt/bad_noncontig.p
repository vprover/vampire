tff(nat_type, type-datatype, nat : $tType).
tff(zero_type, type-datatype_constructor, zero : nat).

tff(unrelated, axiom, ![X : nat]: X = X).

tff(succ_type, type-datatype_constructor, succ : nat > nat).

tff(nat_type, type-datatype, nat : $tType).
tff(zero_type, type-datatype_constructor, zero : nat).
tff(succ_type, type-datatype_constructor, succ : nat > nat).

tff(all_nats_zero_or_succ, conjecture, ![X : nat]: ( X = zero | ?[Y : nat]: X = succ(Y) )).

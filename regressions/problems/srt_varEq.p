% res: sat

tff(sy_c_Groups_Ozero__class_Ozero_001tc__Nat__Onat, type,
    zero_zero_nat : nat).
tff(sy_c_Nat_OSuc, type,
    suc : nat > nat).
tff(sy_c_fFalse, type,
    fFalse : bool).
tff(sy_c_fTrue, type,
    fTrue : bool).
tff(sy_c_pp, type,
    pp : bool > $o).

tff(help_pp_1_1_U, axiom,
    ((~ pp(fFalse)))).
tff(help_pp_2_1_U, axiom,
    (pp(fTrue))).

tff(conj_0, conjecture,
    ((?[U : product_unit, V : product_unit]: (~ U = V)))).
tff(conj_1, conjecture,
    (zero_zero_nat = suc(zero_zero_nat))).
tff(conj_2, conjecture,
    ($false)).

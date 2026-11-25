% Set intersection by its definition (a Sledgehammer TH0 export, reduced). With -fde none -uwa off
% the proof needs a superposition whose unifier is first-order but lies inside a lambda body:
% collect_b @ (^x. member_b x X1 & member_b x X2)  =?  collect_b @ (^x. member_b x sK1 & member_b x sK0).
% RobSubstitution::unify used to refuse to decompose lambdas, so -uwa off gave up.

thf(ty_n_t__Set__Oset_Itf__b_J, type,
    set_b : $tType).
thf(ty_n_tf__b, type,
    b : $tType).
thf(sy_c_Lattices_Oinf__class_Oinf_001t__Set__Oset_Itf__b_J, type,
    inf_inf_set_b : set_b > set_b > set_b).
thf(sy_c_Set_OCollect_001tf__b, type,
    collect_b : (b > $o) > set_b).
thf(sy_c_member_001tf__b, type,
    member_b : b > set_b > $o).
thf(fact_61_Int__def, axiom,
    ((inf_inf_set_b = (^[A3 : set_b]: (^[B3 : set_b]: (collect_b @ (^[X : b]: (((member_b @ X @ A3)) & ((member_b @ X @ B3)))))))))). % Int_def
thf(conj_0, conjecture,
    ((![W : set_b, U : set_b]: ((collect_b @ (^[R4 : b]: (((member_b @ R4 @ U)) & ((member_b @ R4 @ W))))) = (inf_inf_set_b @ U @ W))))).

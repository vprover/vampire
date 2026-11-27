% Reduced from a Sledgehammer TH1 export (HOL-Real_Asymp, Multiseries_Expansion, prob_01674_074972).
% With the ordinary KBO, the sort arguments of the encoding make the monom side of eval_monom_Cons
% heavier (87 vs 80), so it is oriented towards the lambda and cannot fold fact_0; with -hol_fo_kbo
% (f @ a @ b weighs like f(a,b)) it is oriented as in the first-order export and the goal is closed
% by forward demodulation without any activation.
thf(ty_t_Product__Type_Oprod, type,
    product_prod : $tType > $tType > $tType).
thf(ty_t_Filter_Ofilter, type,
    filter : $tType > $tType).
thf(ty_t_Real_Oreal, type,
    real : $tType).
thf(ty_t_List_Olist, type,
    list : $tType > $tType).
thf(ty_t_Set_Oset, type,
    set : $tType > $tType).
thf(sy_c_Filter_Oat__top, type,
    at_top : !>[A : $tType]: (filter @ A)).
thf(sy_c_Groups_Otimes__class_Otimes, type,
    times_times : !>[A : $tType]: (A > A > A)).
thf(sy_c_Landau__Symbols_Osmallo, type,
    landau_smallo : !>[A : $tType, B : $tType]: ((filter @ A) > (A > B) > (set @ (A > B)))).
thf(sy_c_List_Olist_OCons, type,
    cons : !>[A : $tType]: (A > (list @ A) > (list @ A))).
thf(sy_c_Multiseries__Expansion_Oeval__monom, type,
    multis1452009747_monom : (product_prod @ real @ (list @ real)) > (list @ (real > real)) > real > real).
thf(sy_c_Product__Type_OPair, type,
    product_Pair : !>[A : $tType, B : $tType]: (A > B > (product_prod @ A @ B))).
thf(sy_c_Transcendental_Opowr, type,
    powr : !>[A : $tType]: (A > A > A)).
thf(sy_c_member, type,
    member : !>[A : $tType]: (A > (set @ A) > $o)).
thf(sy_v_b, type,
    b : real > real).
thf(sy_v_b_H____, type,
    b2 : real > real).
thf(sy_v_ba____, type,
    ba : real > real).
thf(sy_v_basis, type,
    basis : (list @ (real > real))).
thf(sy_v_basis_H____, type,
    basis2 : (list @ (real > real))).
thf(sy_v_basisa____, type,
    basisa : (list @ (real > real))).
thf(sy_v_c____, type,
    c : real).
thf(sy_v_e, type,
    e : real).
thf(sy_v_e_H____, type,
    e2 : real).
thf(sy_v_ea____, type,
    ea : real).
thf(sy_v_es____, type,
    es : (list @ real)).
thf(sy_v_esa____, type,
    esa : (list @ real)).
thf(sy_v_x, type,
    x : (product_prod @ real @ (list @ real))).
thf(fact_0__092_060open_062_I_092_060lambda_062x_O_Aeval__monom_A_Ic_M_Aes_J_Abasis_H_Ax_A_K_Ab_H_Ax_Apowr_Ae_H_J_A_092_060in_062_Ao_I_092_060lambda_062x_O_Ab_Ax_Apowr_Ae_J_092_060close_062, axiom,
    ((member @ (real > real) @ (^[X : real]: (times_times @ (real) @ (multis1452009747_monom @ (product_Pair @ (real) @ ((list @ real)) @ c @ esa) @ basis2 @ X) @ (powr @ (real) @ (b2 @ X) @ e2))) @ (landau_smallo @ (real) @ (real) @ (at_top @ (real)) @ (^[X : real]: (powr @ (real) @ (ba @ X) @ ea))))), [], [isabelle_rank(900)]). % \<open>(\<lambda>x. eval_monom (c, es) basis' x * b' x powr e') \<in> o(\<lambda>x. b x powr e)\<close>
thf(fact_11_local_OCons, axiom,
    ((basisa = (cons @ (real > real) @ b2 @ basis2))), [], [isabelle_rank(958)]). % local.Cons
thf(fact_34_eval__monom__Cons, axiom,
    ((![C2 : real, E : real, Es2 : (list @ real), B2 : real > real, Basis : (list @ (real > real))]: ((multis1452009747_monom @ (product_Pair @ (real) @ ((list @ real)) @ C2 @ (cons @ (real) @ E @ Es2)) @ (cons @ (real > real) @ B2 @ Basis)) = (^[X : real]: (times_times @ (real) @ (multis1452009747_monom @ (product_Pair @ (real) @ ((list @ real)) @ C2 @ Es2) @ Basis @ X) @ (powr @ (real) @ (B2 @ X) @ E)))))), [], [isabelle_rank(1080)]). % eval_monom_Cons
thf(conj_0, conjecture,
    ((member @ (real > real) @ (multis1452009747_monom @ (product_Pair @ (real) @ ((list @ real)) @ c @ (cons @ (real) @ e2 @ esa)) @ basisa) @ (landau_smallo @ (real) @ (real) @ (at_top @ (real)) @ (^[X : real]: (powr @ (real) @ (ba @ X) @ ea)))))).

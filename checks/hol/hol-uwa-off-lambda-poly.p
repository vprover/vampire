% A type-class guarded fact (a Sledgehammer TH1 export, reduced to the 4 premises of the proof).
% With -uwa off the last superposition unifies ^_. X0 with ^_. zero_zero @ b, which
% RobSubstitution::unify used to refuse, so the problem was given up.

thf(ty_t_Set_Oset, type,
    set : $tType > $tType).
thf(ty_tf_b, type,
    b : $tType).
thf(ty_tf_a, type,
    a : $tType).
thf(sy_cl_Real__Vector__Spaces_Ometric__space, type,
    real_V2090557954_space : !>[A : $tType]: $o).
thf(sy_cl_Topological__Spaces_Otopological__space, type,
    topolo503727757_space : !>[A : $tType]: $o).
thf(sy_cl_Real__Vector__Spaces_Oreal__normed__vector, type,
    real_V55928688vector : !>[A : $tType]: $o).
thf(sy_c_Bounded__Continuous__Function_Obcontfun, type,
    bounde55068707ontfun : !>[A : $tType, B : $tType]: (set @ (A > B))).
thf(sy_c_Groups_Ozero__class_Ozero, type,
    zero_zero : !>[A : $tType]: A).
thf(sy_c_member, type,
    member : !>[A : $tType]: (A > (set @ A) > $o)).
thf(fact_1_const__bcontfun, axiom,
    ((![B : $tType, A : $tType]: (((topolo503727757_space @ (A)) & (real_V2090557954_space @ (B))) => (![B2 : B]: (member @ (A > B) @ (^[X : A]: B2) @ (bounde55068707ontfun @ (A) @ (B))))))), [], [isabelle_rank(905)]). % const_bcontfun
thf(subcl_Real__Vector__Spaces_Oreal__normed__vector___Real__Vector__Spaces_Ometric__space, axiom,
    ((![A : $tType]: ((real_V55928688vector @ (A)) => (real_V2090557954_space @ (A))))), [], [isabelle_inductive]).
thf(tfree_0, hypothesis,
    ((real_V55928688vector @ (b)))).
thf(tfree_1, hypothesis,
    ((topolo503727757_space @ (a)))).
thf(conj_0, conjecture,
    ((member @ (a > b) @ (^[Uu : a]: (zero_zero @ (b))) @ (bounde55068707ontfun @ (a) @ (b))))).

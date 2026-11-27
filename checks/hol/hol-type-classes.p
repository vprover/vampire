% A goal at a type whose class membership needs a chain of type-class axioms (tcon_/subcl_/tfree_
% as in Sledgehammer TH1 exports): with -sos type_classes these stay in active, and only backward
% chaining from the guards can use them (with -sosts on their heads are eligible).
thf(ty_a, type, a : $tType).
thf(ty_star, type, star : $tType > $tType).
thf(ty_pair, type, pair : $tType > $tType > $tType).
thf(sy_cl_s1, type, semiring_1 : !>[A : $tType]: $o).
thf(sy_cl_s0, type, semiring_0 : !>[A : $tType]: $o).
thf(sy_c_r, type, r : !>[A : $tType]: (A > $o)).
thf(sy_c_e, type, e : !>[A : $tType]: A).
thf(tcon_star, axiom, ![A : $tType]: ((semiring_1 @ A) => (semiring_1 @ (star @ A)))).
thf(tcon_pair, axiom, ![A : $tType, B : $tType]: (((semiring_1 @ A) & (semiring_1 @ B)) => (semiring_1 @ (pair @ A @ B)))).
thf(subcl, axiom, ![A : $tType]: ((semiring_1 @ A) => (semiring_0 @ A))).
thf(tfree_0, hypothesis, (semiring_1 @ a)).
thf(fact, axiom, ![A : $tType]: ((semiring_0 @ A) => (r @ A @ (e @ A)))).
thf(conj, conjecture, (r @ (pair @ a @ (star @ a)) @ (e @ (pair @ a @ (star @ a))))).

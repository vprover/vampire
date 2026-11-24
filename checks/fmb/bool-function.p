% A function into $o in the printed model. FOOL elimination names the boolean argument r(X)
% of q by a function bG0 : $i > $o, and predicate elimination defines q (and, under -pel
% multi, r) over bG0, so -fmbmp layered prints bG0 too. Declared bG0 : $i > $o, though,
% TPTP reads it as a predicate, so its table has to be printed as one -- bG0('fmb_$i_1') &
% ~bG0('fmb_$i_2') -- rather than as the function it is in Vampire's signature:
% bG0('fmb_$i_1') = $true read back as an equation between formulas, which model_check
% refused ("Cannot read the definition"). Seen first on Problems/CSR/CSR141_8.p.

tff(q_type,type,q: ($i * $o) > $o).
tff(p_type,type,p: $i > $o).
tff(r_type,type,r: $i > $o).
tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(def, axiom, ! [X: $i] : ( p(X) => q(X, r(X)) )).
tff(use1, axiom, p(a)).
tff(use2, axiom, ~ q(b, $true)).
tff(use3, axiom, r(a) | r(b)).

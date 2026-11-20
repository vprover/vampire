% The model -fmbmp layered prints for fmb/bool-function.p under -pel multi, read back: bG0,
% a function into $o, is printed as the predicate TPTP reads it as.
%
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

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2'
).

tff(finite_domain_bool,axiom,
      ! [X:$o] : (
         (X = $false) | (X = $true)
      ) ).

tff(distinct_domain_bool,axiom,
         $false != $true
).

tff(declare_a,type,a : $i).
tff(declare_b,type,b : $i).
tff(declare_q,type,q: ( $i * $o ) > $o ).
tff(declare_p,type,p: ( $i ) > $o ).
tff(declare_r,type,r: ( $i ) > $o ).
tff(declare_bG0,type,bG0 : ( $i ) > $o).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(q_symbolic_definition,axiom,![X0:$i, X1:$o]: (q(X0,X1) <=> (? [X2:$i] : (p(X2) & (bG0(X2) = X1) & (X0 = X2))))).
tff(p_symbolic_definition,axiom,![X0:$i]: (p(X0) <=> (a = X0))).
tff(r_symbolic_definition,axiom,![X0:$i]: (r(X0) <=> (! [X1:$i] : (($true = bG0(X1)) | (X0 != X1))))).
tff(predicate_bG0,axiom,
           bG0('fmb_$i_1')
         & bG0('fmb_$i_2')
).

vampire(model_check,model_end).

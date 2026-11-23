% The model -fmbmp layered prints for fmb/cond-flip.p under -bce on, read back: r is defined
% over its earlier version 'r_$1'.
%
% A conditional flip, printed by -fmbmp layered as what it is: a definition of the
% predicate over the version of it below the flip.
%
% Under -bce on, c1 is blocked on r(X,Y) (its only resolvent on r, with c2, is a tautology),
% so it is eliminated, and the model reconstruction undoes that by a flip: wherever c1 is
% false, i.e. s holds of both arguments and r does not, make r true. The model prints r as
% r(X0,X1) <=> ('r_$1'(X0,X1) | ~(~s(X1) | ~s(X0) | 'r_$1'(X0,X1))), 'r_$1' being r before
% the flip, a table. Before, r was spelled out as a table, and later as a $cond listing the
% tuples the flip changes -- which is what a flip needing a fixed point still is (see
% fmb/cond-flip-fixpoint.p).

cnf(c1, axiom, r(X,Y) | ~s(X) | ~s(Y)).
cnf(c2, axiom, ~r(X,Y) | s(X) | t(Y)).
cnf(c3, axiom, ~s(a) | t(a)).
cnf(c4, axiom, s(b)).
cnf(c5, axiom, r(a,b) | r(b,a)).
cnf(c6, axiom, ~t(b) | ~t(a)).

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

tff(declare_a,type,a : $i).
tff(declare_b,type,b : $i).
tff(declare_r,type,r: ( $i * $i ) > $o ).
tff(declare_s,type,s: ( $i ) > $o ).
tff(declare_t,type,t: ( $i ) > $o ).
tff('declare_r_$1',type,'r_$1': ( $i * $i ) > $o ).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(r_symbolic_definition,axiom,![X0:$i, X1:$i]: (r(X0,X1) <=> ('r_$1'(X0,X1) | ~((~s(X1) | ~s(X0) | 'r_$1'(X0,X1)))))).
tff(predicate_s,axiom,
           ~s('fmb_$i_1')
         & s('fmb_$i_2')
).

tff(predicate_t,axiom,
           t('fmb_$i_1')
         & ~t('fmb_$i_2')
).

tff('predicate_r_$1',axiom,
           ~'r_$1'('fmb_$i_1','fmb_$i_1')
         & 'r_$1'('fmb_$i_2','fmb_$i_1')
         & ~'r_$1'('fmb_$i_1','fmb_$i_2')
         & ~'r_$1'('fmb_$i_2','fmb_$i_2')
).

vampire(model_check,model_end).

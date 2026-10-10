% $cond in the formulas --mode model_check evaluates against a loaded model. The model
% itself is an ordinary explicit table (that is all ModelCheck can read today); what is
% under test is that FiniteModelMultiSorted evaluates the $cond in the *problem*.
%
% The conditions overlap on 'fmb_$i_1' and 'fmb_$i_3', where p and q both hold, so the
% formula holds in this model only if the first match wins: there f must be a, not b.

tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(c_type,type,c: $i).
tff(f_type,type,f: $i > $i).
tff(p_type,type,p: $i > $o).
tff(q_type,type,q: $i > $o).

tff(f_def,axiom,
    ! [X: $i] : f(X) = $cond(p(X), a, q(X), b, c) ).

% ... and once more in formula position
tff(overlap,axiom,
    ? [X: $i] : $cond(p(X), q(X), $false) ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('declare_$i3',type,'fmb_$i_3':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2') | (X = 'fmb_$i_3')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2' & 'fmb_$i_1' != 'fmb_$i_3' & 'fmb_$i_2' != 'fmb_$i_3'
).

tff(declare_a,type,a : $i).
tff(a_definition,axiom,a = 'fmb_$i_1').
tff(declare_b,type,b : $i).
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(declare_c,type,c : $i).
tff(c_definition,axiom,c = 'fmb_$i_3').

tff(declare_f,type,f : ( $i ) > $i).
tff(function_f,axiom,
           f('fmb_$i_1') = 'fmb_$i_1'
         & f('fmb_$i_2') = 'fmb_$i_3'
         & f('fmb_$i_3') = 'fmb_$i_1'
).

tff(declare_p,type,p: ( $i ) > $o ).
tff(predicate_p,axiom,
           p('fmb_$i_1')
         & ~p('fmb_$i_2')
         & p('fmb_$i_3')
).

tff(declare_q,type,q: ( $i ) > $o ).
tff(predicate_q,axiom,
           q('fmb_$i_1')
         & ~q('fmb_$i_2')
         & q('fmb_$i_3')
).

vampire(model_check,model_end).

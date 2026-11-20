% The model -fmbmp layered prints for fmb/cond.p (fmb/cond.layered.out), read back.
% f is printed by its definition f(X0) = iG1(X0), so the introduced iG1 must be printed too,
% or model_check cannot evaluate f. (The explicit printing leaves iG1 out, which is why
% fmb/cond.check.p carries a hand-made table for f instead.)
%
% FOOLElimination compiles the $cond away before FMB ever runs, but the model self-check
% (FMB_CHECK_MODEL_AGAINST_INPUT) evaluates the *input* units, which still contain it. So
% this is what makes FiniteModelMultiSorted::evaluateTerm need a COND case: without one the
% self-check dies with "Cannot evaluate ..., not supported".
%
% The conditions deliberately overlap -- some element satisfies both p and q -- so the model
% is only consistent with the input if the evaluator lets the first match win.

tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(c_type,type,c: $i).
tff(f_type,type,f: $i > $i).
tff(p_type,type,p: $i > $o).
tff(q_type,type,q: $i > $o).

tff(distinct,axiom,
    a != b & b != c & a != c ).

tff(f_def,axiom,
    ! [X: $i] : f(X) = $cond(p(X), a, q(X), b, c) ).

tff(overlap,axiom,
    ? [X: $i] : ( p(X) & q(X) ) ).

tff(somewhere_neither,axiom,
    ? [X: $i] : ( ~p(X) & ~q(X) ) ).

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
tff(declare_b,type,b : $i).
tff(declare_c,type,c : $i).
tff(declare_f,type,f : ( $i ) > $i).
tff(declare_p,type,p: ( $i ) > $o ).
tff(declare_q,type,q: ( $i ) > $o ).
tff(declare_iG1,type,iG1 : ( $i ) > $i).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(c_definition,axiom,c = 'fmb_$i_3').
tff(f_symbolic_definition,axiom,![X0:$i]: f(X0) = iG1(X0)).
tff(predicate_p,axiom,
           p('fmb_$i_1')
         & ~p('fmb_$i_2')
         & p('fmb_$i_3')
).

tff(predicate_q,axiom,
           q('fmb_$i_1')
         & ~q('fmb_$i_2')
         & q('fmb_$i_3')
).

tff(function_iG1,axiom,
           iG1('fmb_$i_1') = 'fmb_$i_1'
         & iG1('fmb_$i_2') = 'fmb_$i_3'
         & iG1('fmb_$i_3') = 'fmb_$i_1'
).

vampire(model_check,model_end).

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

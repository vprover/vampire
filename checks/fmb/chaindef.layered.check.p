% The model -fmbmp layered prints for fmb/chaindef.p under -fde unused, read back.
% f is defined by g and printed first, g by h after it: model_check has to add the
% definitions in dependency order, not in the order they come in the file.
%
% Two chained unused function definitions, the dependent one stated first.
%
% -fde unused removes f (it occurs only in its own definition), which makes g unused in
% turn, so g goes as well. The recorded definitions are therefore f(X):=g(X) and g(X):=h(X),
% and a model reconstruction replaying them backwards must restore g *before* f -- f's body
% reads g, so evaluating it any earlier reads whatever the model happened to say about a g
% that has not been defined yet.
%
% removeUnusedDefinitions used to record by popping defStack, which is the order the clauses
% were scanned, rather than the order of the toDo loop that actually performs the removal in
% dependency order. Swapping the two clauses in this file hid the defect, which is what makes
% it worth pinning: the exact output below is the replay order.
%
% The last two clauses are only here to keep the clause set non-empty and satisfiable after
% the eliminations, so that saturation reports a model and prints the recorded definitions.

cnf(c1,axiom,
    f(X) = g(X) ).

cnf(c2,axiom,
    g(X) = h(X) ).

cnf(c3,axiom,
    p(h(a)) ).

cnf(c4,axiom,
    ~ p(b) ).

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

tff(declare_f,type,f : ( $i ) > $i).
tff(declare_g,type,g : ( $i ) > $i).
tff(declare_h,type,h : ( $i ) > $i).
tff(declare_a,type,a : $i).
tff(declare_b,type,b : $i).
tff(declare_p,type,p: ( $i ) > $o ).

tff(f_symbolic_definition,axiom,![X0:$i]: f(X0) = g(X0)).
tff(g_symbolic_definition,axiom,![X0:$i]: g(X0) = h(X0)).
tff(function_h,axiom,
           h('fmb_$i_1') = 'fmb_$i_2'
         & h('fmb_$i_2') = 'fmb_$i_2'
).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_1').
tff(predicate_p,axiom,
           ~p('fmb_$i_1')
         & p('fmb_$i_2')
).

vampire(model_check,model_end).

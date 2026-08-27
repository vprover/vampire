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

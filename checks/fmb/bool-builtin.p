% Under -newcnf on, ![X:$o]: (X | ~X) is expanded over $true and $false at clausification,
% and nothing of $o is left in the clauses. The domain of $o is built in all the same, on
% both sides: FMB gives it its two elements (FMB/FiniteModelBuilder.cpp, onModelFound) and
% prints them; model_check, reading a model that leaves the domain of $o out -- as the empty
% one in bool-builtin.check.p, which FMB itself printed at first -- uses the built-in one
% (FMB/ModelCheck.hpp). Earlier, model_check said
% "Cannot evaluate a boolean term: this model does not have a boolean domain".
% (Taken from Problems/SYN/SYN989_8.p.)
tff(thm,axiom,
    ! [X: $o] : ( X | ~ X ) ).

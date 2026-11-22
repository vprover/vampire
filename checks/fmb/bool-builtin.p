% Under -newcnf on, ![X:$o]: (X | ~X) is expanded over $true and $false at clausification,
% nothing of $o is left, and FMB prints an empty model. model_check has to know the domain
% of $o anyway: it is built in, not something the model chooses (FMB/ModelCheck.hpp).
% Earlier: "Cannot evaluate a boolean term: this model does not have a boolean domain".
% (Taken from Problems/SYN/SYN989_8.p.)
tff(thm,axiom,
    ! [X: $o] : ( X | ~ X ) ).

% A model may spell out the domain of $o, but it has to be the built-in one, $false and
% $true (FMB/ModelCheck.hpp): this one would make $o a singleton.
tff(thm,axiom, ! [X: $o] : ( X | ~ X ) ).
vampire(model_check,model_start).
tff(finite_domain_bool,axiom, ! [X:$o] : ( X = $true ) ).
vampire(model_check,model_end).

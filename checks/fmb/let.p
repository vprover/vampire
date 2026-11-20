% $let in the input. FOOL elimination compiles it away before FMB runs, so FMB finds a model;
% what has to cope with it is everything that reads the input as parsed:
% - the self-check cannot evaluate a $let and must skip those units, saying so;
% - the printer must not take :=, the polymorphic predicate the parser writes a $let binding
%   with (Signature::getDefPred), for a symbol of the problem -- it used to, and asserted on
%   its type variable while printing the model, after the SZS status line;
% - model_check must refuse the units as unsupported (see fmb/let.check.p).
% The function binding captures the outer Y, the case a future evaluator of $let would have
% to get right.

tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(p_type,type,p: $i > $o).

tff(distinct,axiom, a != b ).

tff(captures,axiom,
    ! [Y: $i] : $let(f: $i > $i, f(X) := Y, ( p(f(a)) | ~p(Y) )) ).

tff(constant,axiom,
    $let(c: $i, c := a, p(c)) ).

% As let-bool.p, but the bound Boolean symbol takes an argument, so the
% definition is quantified over it. Also shadows a global of the same name.
tff(r,type,
    r: $int > $o ).

tff(let_bool_pred,conjecture,
    $let(r: $int > $o,
      r(X) := ( r(X) | ~ r(X) ),
      r(1) ) ).

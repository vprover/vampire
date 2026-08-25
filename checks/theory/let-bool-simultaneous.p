% Two symbols bound in one $let, one Boolean and one not, so endLet builds a
% definition for each. On master this shape is a sort error, not a crash.
tff(let_bool_simultaneous,conjecture,
    $let(
      [ b: $o, k: $int ],
      [ b := $true, k := 1 ],
      ( b
      & $greater(k,0) ) ) ).

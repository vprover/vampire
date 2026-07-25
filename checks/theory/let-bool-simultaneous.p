% Two Boolean symbols bound in one $let, so endLet builds a definition for each.
% One of them is Boolean and one is not, which used to give a sort error rather
% than a crash.
tff(let_bool_simultaneous,conjecture,
    $let(
      [ b: $o, k: $int ],
      [ b := $true, k := 1 ],
      ( b
      & $greater(k,0) ) ) ).

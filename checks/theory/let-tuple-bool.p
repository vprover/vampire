
tff(p_type, type, p: !>[A: $tType, B: $tType]: (A * B) > $o).
tff(f_type, type, f: !>[A: $tType, B: $tType]: (A * B) > [A, B]).
tff(c_type, type, c: !>[A: $tType]: A).
tff(d_type, type, d: !>[A: $tType]: A).

tff(conj,conjecture,
    $let(
      [ p1: $o, p2: $o ],
      [p1,p2] := [$true,$false],
      p1 != p2 ) ).

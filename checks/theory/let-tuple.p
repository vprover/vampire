
tff(p_type, type, p: !>[A: $tType, B: $tType]: (A * B) > $o).
tff(f_type, type, f: !>[A: $tType, B: $tType]: (A * B) > [A, B]).
tff(c_type, type, c: !>[A: $tType]: A).
tff(d_type, type, d: !>[A: $tType]: A).

tff(ax,axiom,
    ! [A: $tType, B: $tType] :
    $let(
      [ a: A, b: B ],
      [a,b] := [c(A),d(B)],
      p(A,B,a,b) ) ).

tff(ax2,axiom,
    ! [A: $tType, X: A, B: $tType, Y: B] : f(A,B,X,Y) = [X,Y]).

tff(conj,conjecture,
    ! [A: $tType, B: $tType, C: $tType] :
     $let(
       [ a: A, b: C ],
       [a,b] := f(A,C,c(A),d(C)),
       p(A,C,a,b) ) ).

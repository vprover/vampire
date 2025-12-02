
tff(c_type, type, c: !>[A: $tType]: A).
tff(d_type, type, d: !>[A: $tType]: A).
tff(f_type, type, f: !>[A: $tType, B: $tType]: ((A * B) > A)).
tff(p_type, type, p: !>[A: $tType]: A > $o).

tff(ax, axiom,
    ! [A: $tType, C: $tType] : 
      $let(
        const : !>[B: $tType] : (A * B) > A,
        const(B, X, Y) := X,
        p(A, const(C, c(A), d(C)))) ).

tff(conj, conjecture,
    ! [A: $tType, C: $tType, Z : C] :
      (f(A, C, c(A), Z) = c(A) =>
       $let(
         const : !>[B: $tType] : (A * B) > A,
         const(B, X, Y) := f(A, C, X, Z),
         p(A, const(C, c(A), d(C))))) ).

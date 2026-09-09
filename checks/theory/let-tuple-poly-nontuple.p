%----A polymorphic tuple binding whose right hand side is not a tuple
%----literal: the fresh symbol standing for it takes the type variables of
%----the tuple sort as arguments.
tff(p_type,type,p: !>[A: $tType, B: $tType]: (A * B) > $o).
tff(f_type,type,f: !>[A: $tType, B: $tType]: (A * B) > [A, B]).
tff(c_type,type,c: !>[A: $tType]: A).
tff(d_type,type,d: !>[A: $tType]: A).
tff(ax,axiom, ! [A: $tType, B: $tType, X: A, Y: B] : f(A,B,X,Y) = [X,Y]).
tff(ax2,axiom, ! [A: $tType, B: $tType] : p(A,B,c(A),d(B))).
tff(c,conjecture,
    ! [A: $tType, B: $tType] :
     $let([ a: A, b: B ],
       [a,b] := f(A,B,c(A),d(B)),
       p(A,B,a,b) ) ).

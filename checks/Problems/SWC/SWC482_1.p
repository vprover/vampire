%------------------------------------------------------------------------------
% File     : SWC482_1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Software Creation
% Problem  : Prove equivalence of small and fast program for sequence A272134
% Version  : Especial.
% English  : Terms: 0 4 68 282 736 1520 2724 4438 6752 9756 13540 18194 23808 
%            30472 38276 47310 57664 69428 82692 97546
%            Small: (2+(2+((loop(x*x,2,2)-1)*((x*x)-x))))*x
%            Fast : ((loop(x*x,1,2-(2*(x+x)))-(x*x))+x)*x

% Refs     : [GB+23] Gauthier et al. (2023), A Mathematical Benchmark for I
%          : [Git23] https://github.com/ai4reason/oeis-atp-benchmark
% Source   : [Git23]
% Names    : A272134 [Git23]

% Status   : Theorem
% Rating   : 0.38 v9.0.0
% Syntax   : Number of formulae    :   25 (  10 unt;  12 typ;   0 def)
%            Number of atoms       :   20 (  15 equ)
%            Maximal formula atoms :    4 (   1 avg)
%            Number of connectives :   11 (   4   ~;   0   |;   3   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   3 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number arithmetic     :   49 (   5 atm;  18 fun;  15 num;  11 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :   10 (   8   >;   2   *;   0   +;   0  <<)
%            Number of predicates  :    3 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   18 (  12 usr;   7 con; 0-2 aty)
%            Number of variables   :   11 (;  10   !;   1   ?;  11   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Not in an "aind_*" subset, i.e., unlikely to require induction.
%------------------------------------------------------------------------------
tff(u1,type,
    u1: ( $int * $int ) > $int ).

tff(u0,type,
    u0: ( $int * $int ) > $int ).

tff(v1,type,
    v1: $int > $int ).

tff(v0,type,
    v0: $int ).

tff(h1,type,
    h1: $int > $int ).

tff(h0,type,
    h0: $int ).

tff(g1,type,
    g1: $int ).

tff(fast,type,
    fast: $int > $int ).

tff(g0,type,
    g0: $int ).

tff(small,type,
    small: $int > $int ).

tff(f0,type,
    f0: $int > $int ).

tff(f1,type,
    f1: $int > $int ).

%----∀ x:Int (f0(x) = (x * x))
tff(formula_1,axiom,
    ! [X: $int] : ( f0(X) = $product(X,X) ) ).

%----(g0 = 2)
tff(formula_2,axiom,
    g0 = 2 ).

%----(h0 = 2)
tff(formula_3,axiom,
    h0 = 2 ).

%----∀ x:Int y:Int (u0(x, y) = (if (x ≤ 0) y else f0(u0((x - 1), y))))
tff(formula_4,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
       => ( u0(X,Y) = Y ) )
      & ( ~ $lesseq(X,0)
       => ( u0(X,Y) = f0(u0($difference(X,1),Y)) ) ) ) ).

%----(v0 = u0(g0, h0))
tff(formula_5,axiom,
    v0 = u0(g0,h0) ).

%----∀ x:Int (small(x) = ((2 + (2 + ((v0 - 1) * ((x * x) - x)))) * x))
tff(formula_6,axiom,
    ! [X: $int] : ( small(X) = $product($sum(2,$sum(2,$product($difference(v0,1),$difference($product(X,X),X)))),X) ) ).

%----∀ x:Int (f1(x) = (x * x))
tff(formula_7,axiom,
    ! [X: $int] : ( f1(X) = $product(X,X) ) ).

%----(g1 = 1)
tff(formula_8,axiom,
    g1 = 1 ).

%----∀ x:Int (h1(x) = (2 - (2 * (x + x))))
tff(formula_9,axiom,
    ! [X: $int] : ( h1(X) = $difference(2,$product(2,$sum(X,X))) ) ).

%----∀ x:Int y:Int (u1(x, y) = (if (x ≤ 0) y else f1(u1((x - 1), y))))
tff(formula_10,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
       => ( u1(X,Y) = Y ) )
      & ( ~ $lesseq(X,0)
       => ( u1(X,Y) = f1(u1($difference(X,1),Y)) ) ) ) ).

%----∀ x:Int (v1(x) = u1(g1, h1(x)))
tff(formula_11,axiom,
    ! [X: $int] : ( v1(X) = u1(g1,h1(X)) ) ).

%----∀ x:Int (fast(x) = (((v1(x) - (x * x)) + x) * x))
tff(formula_12,axiom,
    ! [X: $int] : ( fast(X) = $product($sum($difference(v1(X),$product(X,X)),X),X) ) ).

%----∃ c:Int ((c ≥ 0) ∧ ¬(small(c) = fast(c)))
tff(conjecture_1,conjecture,
    ~ ? [C: $int] :
        ( $greatereq(C,0)
        & ( small(C) != fast(C) ) ) ).

%------------------------------------------------------------------------------

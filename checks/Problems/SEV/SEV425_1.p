%------------------------------------------------------------------------------
% File     : SEV425_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Set Theory
% Problem  : Allocating and inserting at least three objects
% Version  : Especial.
% English  : Allocating and inserting at least three objects into a container
%            data structure.

% Refs     : [KNR07] Kuncak et al. (2007), Deciding Boolean Algebra with Pr
%          : [KR07]  Kuncak & Rinard (2007), Towards Efficient Satisfiabili
% Source   : [KR07]
% Names    : VC#5 [KR07]

% Status   : Theorem
% Rating   : 0.62 v8.2.0, 0.75 v7.5.0, 0.80 v7.4.0, 0.75 v7.3.0, 0.83 v7.0.0, 1.00 v5.5.0, 0.89 v5.4.0, 0.88 v5.3.0, 1.00 v5.0.0
% Syntax   : Number of formulae    :   24 (   0 unt;  11 typ;   0 def)
%            Number of atoms       :   35 (  13 equ)
%            Maximal formula atoms :    7 (   1 avg)
%            Number of connectives :   28 (   6   ~;   1   |;   7   &)
%                                         (  12 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   15 (   6 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number arithmetic     :    7 (   0 atm;   3 fun;   4 num;   0 var)
%            Number of types       :    4 (   2 usr;   1 ari)
%            Number of type conns  :   13 (   8   >;   5   *;   0   +;   0  <<)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :   11 (   7 usr;   4 con; 0-2 aty)
%            Number of variables   :   34 (  34   !;   0   ?;  34   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(set_type,type,
    set: $tType ).

tff(element_type,type,
    element: $tType ).

tff(empty_set_type,type,
    empty_set: set ).

tff(singleton_type,type,
    singleton: element > set ).

tff(member_type,type,
    member: ( element * set ) > $o ).

tff(subset_type,type,
    subset: ( set * set ) > $o ).

tff(intersection_type,type,
    intersection: ( set * set ) > set ).

tff(union_type,type,
    union: ( set * set ) > set ).

tff(difference_type,type,
    difference: ( set * set ) > set ).

tff(complement_type,type,
    complement: set > set ).

tff(cardinality_type,type,
    cardinality: set > $int ).

tff(empty_set,axiom,
    ! [S: set] :
      ( ! [X: element] : ~ member(X,S)
    <=> ( S = empty_set ) ) ).

tff(singleton,axiom,
    ! [X: element,A: element] :
      ( member(X,singleton(A))
    <=> ( X = A ) ) ).

tff(subset,axiom,
    ! [A: set,B: set] :
      ( subset(A,B)
    <=> ! [X: element] :
          ( member(X,A)
         => member(X,B) ) ) ).

tff(intersection,axiom,
    ! [X: element,A: set,B: set] :
      ( member(X,intersection(A,B))
    <=> ( member(X,A)
        & member(X,B) ) ) ).

tff(union,axiom,
    ! [X: element,A: set,B: set] :
      ( member(X,union(A,B))
    <=> ( member(X,A)
        | member(X,B) ) ) ).

tff(difference,axiom,
    ! [B: element,A: set,E: set] :
      ( member(B,difference(E,A))
    <=> ( member(B,E)
        & ~ member(B,A) ) ) ).

tff(complement,axiom,
    ! [X: element,S: set] :
      ( member(X,S)
    <=> ~ member(X,complement(S)) ) ).

%----From Swen (combined two of his)
tff(cardinality_empty_set,axiom,
    ! [S: set] :
      ( ( cardinality(S) = 0 )
    <=> ( S = empty_set ) ) ).

tff(cardinality_intersection_1,axiom,
    ! [X: element,S: set] :
      ( ( intersection(singleton(X),S) = singleton(X) )
    <=> ( cardinality(union(singleton(X),S)) = cardinality(S) ) ) ).

tff(cardinality_intersection_2,axiom,
    ! [X: element,S: set] :
      ( ( intersection(singleton(X),S) = empty_set )
    <=> ( cardinality(union(singleton(X),S)) = $sum(cardinality(S),1) ) ) ).

tff(cardinality_intersection_3,axiom,
    ! [S: set,T: set] :
      ( ( cardinality(intersection(S,T)) = 0 )
    <=> ( intersection(S,T) = empty_set ) ) ).

%----From Swen, modified to <=>
tff(cardinality_union,axiom,
    ! [A: set,B: set] :
      ( ( intersection(A,B) = empty_set )
    <=> ( cardinality(union(A,B)) = $sum(cardinality(A),cardinality(B)) ) ) ).

tff(vc5,conjecture,
    ! [C: set,A0: set,A1: set,A2: set,X1: element,X2: element,X3: element] :
      ( ( subset(C,A0)
        & ~ member(X1,A0)
        & subset(union(A0,singleton(X1)),A1)
        & ~ member(X2,A1)
        & subset(union(A1,singleton(X2)),A2)
        & ~ member(X3,A2) )
     => ( cardinality(union(union(union(C,singleton(X1)),singleton(X2)),singleton(X3))) = $sum(cardinality(C),3) ) ) ).

%------------------------------------------------------------------------------

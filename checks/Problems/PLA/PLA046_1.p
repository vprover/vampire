%------------------------------------------------------------------------------
% File     : PLA046_1 : TPTP v9.0.0. Released v7.3.0.
% Domain   : Planning
% Problem  : Expected number of steps to proof of optimality - local
% Version  : Especial.
% English  : Assume search space is ct(10)=1; ct(9)=2; ...; ct(1) = 10
%            Initial dist from opt = 10.  Assume only inc1 and dec1 have 
%            increased probability.

% Refs     : [Wal18] Wallace (2018), Email to Geoff Sutcliffe
% Source   : [Wal18]
% Names    : local-search-theorem-for-tptp [Wal18]

% Status   : ContradictoryAxioms
% Rating   : 1.00 v9.0.0, 0.88 v8.1.0, 1.00 v7.5.0, 0.90 v7.4.0, 0.75 v7.3.0
% Syntax   : Number of formulae    :   11 (   4 unt;   4 typ;   0 def)
%            Number of atoms       :   12 (   6 equ)
%            Maximal formula atoms :    4 (   1 avg)
%            Number of connectives :    5 (   0   ~;   0   |;   2   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   3 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number arithmetic     :   83 (   6 atm;  32 fun;  34 num;  11 var)
%            Number of types       :    2 (   0 usr;   2 ari)
%            Number of type conns  :   11 (   4   >;   7   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   19 (   4 usr;  11 con; 0-3 aty)
%            Number of variables   :   11 (  11   !;   0   ?;  11   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(recf,type,
    recf: ( $int * $real * $int ) > $real ).

tff(mysum,type,
    mysum: ( $int * $real ) > $real ).

tff(pp,type,
    pp: ( $int * $real * $int ) > $real ).

tff(zc,type,
    zc: ( $int * $real * $int ) > $real ).

tff(local_search,conjecture,
    ! [Z: $real] :
      ( ( $lesseq(110.0,recf(10,Z,110))
        & $lesseq(0.9,Z)
        & $lesseq(Z,10.0) )
     => $lesseq(Z,1.0) ) ).

tff(zc_n,axiom,
    ! [M: $int,Z: $real] : ( $product($to_real($difference(110,$product(2,M))),zc(M,Z,110)) = $difference(110.0,$product(Z,$to_real($product(2,M)))) ) ).

tff(pp_n,axiom,
    ! [M: $int,Z: $real] : ( $product(110.0,pp(M,Z,110)) = $sum($product(Z,$to_real($difference(M,1))),$product(zc(M,Z,110),$product(0.5,$to_real($product($difference(M,2),$difference(M,1)))))) ) ).

tff(recf_1,axiom,
    ! [Z: $real] : ( recf(1,Z,110) = 0.0 ) ).

tff(recf_n,axiom,
    ! [M: $int,Z: $real] :
      ( $lesseq(2,M)
     => ( $product(pp(M,Z,110),recf(M,Z,110)) = $sum(1.0,$sum($product(recf($difference(M,1),Z,110),$product(Z,$to_real($difference(M,1)))),$product(zc(M,Z,110),mysum(M,Z)))) ) ) ).

tff(mysum_0,axiom,
    ! [Z: $real] : ( mysum(0,Z) = 0.0 ) ).

tff(mysum_n,axiom,
    ! [M: $int,Z: $real] :
      ( $lesseq(1,M)
     => ( mysum(M,Z) = $sum(mysum($difference(M,1),Z),$product(recf(M,Z,110),$to_real(M))) ) ) ).

%------------------------------------------------------------------------------

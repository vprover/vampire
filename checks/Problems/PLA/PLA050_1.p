%------------------------------------------------------------------------------
% File     : PLA050_1 : TPTP v9.0.0. Released v7.3.0.
% Domain   : Planning
% Problem  : Expected number of steps to proof of optimality - thm-4
% Version  : Especial.
% English  : Number of fitness values  and total number of solns unconstrained.
%            Number of solns at each fitness level not given but increases with 
%            distance from optimum. Initial distance anything up to half the 
%            number of fitness values. Assume only inc1 and dec1 have increased 
%            probability.

% Refs     : [Wal18] Wallace (2018), Email to Geoff Sutcliffe
% Source   : [Wal18]
% Names    : ls-thm-4 [Wal18]

% Status   : Theorem
% Rating   : 0.62 v9.0.0, 0.75 v7.5.0, 0.90 v7.4.0, 0.88 v7.3.0
% Syntax   : Number of formulae    :   28 (  10 unt;  10 typ;   0 def)
%            Number of atoms       :   36 (  17 equ)
%            Maximal formula atoms :    9 (   1 avg)
%            Number of connectives :   18 (   0   ~;   0   |;  10   &)
%                                         (   0 <=>;   8  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   4 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number arithmetic     :  142 (  19 atm;  49 fun;  40 num;  34 var)
%            Number of types       :    2 (   0 usr;   2 ari)
%            Number of type conns  :   20 (   8   >;  12   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   21 (  10 usr;   9 con; 0-4 aty)
%            Number of variables   :   34 (  34   !;   0   ?;  34   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(lk,type,
    lk: $int > $int ).

tff(ns,type,
    ns: $int > $int ).

tff(dc_type,type,
    dc: ( $real * $int * $int ) > $real ).

tff(imp,type,
    imp: ( $real * $int * $int ) > $real ).

tff(recexp,type,
    recexp: ( $real * $int * $int ) > $real ).

tff(mylk,type,
    mylk: $int > $int ).

tff(mysumr,type,
    mysumr: ( $real * $int * $int * $int ) > $real ).

tff(mysump,type,
    mysump: ( $real * $int * $int * $int ) > $real ).

tff(problen,type,
    problen: $int ).

tff(probsize,type,
    probsize: $int ).

tff(tougher_local_search,conjecture,
    ! [S: $real,C: $int,Problen: $int,Probsize: $int] :
      ( ( $lesseq(2,Problen)
        & ( problen = Problen )
        & $lesseq($product(Problen,Problen),Probsize)
        & ( probsize = Probsize )
        & $lesseq($product(C,2),problen)
        & $lesseq($to_real(probsize),recexp(S,probsize,C))
        & $lesseq(0.9,S)
        & $lesseq(S,10.0) )
     => $lesseq(S,1.0) ) ).

tff(lk_0,axiom,
    lk(0) = 1 ).

tff(lk_n,axiom,
    ! [K: $int] :
      ( ( $lesseq(1,K)
        & $lesseq(K,problen) )
     => $lesseq(lk($difference(K,1)),lk(K)) ) ).

tff(ns_0,axiom,
    ns(0) = $sum(lk(0),lk(1)) ).

tff(ns_pl,axiom,
    ns(problen) = $sum(lk($difference(problen,1)),lk(problen)) ).

tff(ns_n,axiom,
    ! [K: $int] :
      ( ( $lesseq(1,K)
        & $lesseq(K,$difference(problen,1)) )
     => ( ns(K) = $sum($sum(lk($difference(K,1)),lk(K)),lk($sum(K,1))) ) ) ).

tff(dc,axiom,
    ! [D: $real,T: $int,C: $int] : ( $product(dc(D,T,C),$to_real($difference(T,ns(C)))) = $difference($to_real(T),$product(D,$to_real(ns(C)))) ) ).

tff(imp_0,axiom,
    ! [D: $real,T: $int] : ( imp(D,T,0) = 0.0 ) ).

tff(imp_n,axiom,
    ! [D: $real,T: $int,C: $int] :
      ( $lesseq(1,C)
     => ( $product($to_real(T),imp(D,T,C)) = $sum($product(D,$to_real(lk($difference(C,1)))),mysump(D,T,C,$difference(C,2))) ) ) ).

tff(mysump_0,axiom,
    ! [D: $real,T: $int,C: $int] : ( mysump(D,T,C,0) = 0.0 ) ).

tff(mysump_n,axiom,
    ! [D: $real,T: $int,C: $int,K: $int] :
      ( $lesseq(1,K)
     => ( mysump(D,T,C,K) = $sum($product(dc(D,T,C),$to_real(lk(K))),mysump(D,T,C,$difference(K,1))) ) ) ).

tff(recexp_0,axiom,
    ! [D: $real,T: $int] : ( recexp(D,T,0) = 0.0 ) ).

tff(recexp_n,axiom,
    ! [D: $real,T: $int,C: $int] :
      ( $lesseq(1,C)
     => ( $product(imp(D,T,C),$product($to_real(T),recexp(D,T,C))) = $sum($sum($to_real(T),$product($product(D,recexp(D,T,$difference(C,1))),$to_real(lk($difference(C,1))))),mysumr(D,T,C,$difference(C,2))) ) ) ).

tff(mylk_0,axiom,
    mylk(0) = 1 ).

tff(mylk_n,axiom,
    ! [K: $int] :
      ( ( $lesseq(1,K)
        & $lesseq(K,problen) )
     => ( mylk(K) = $sum(lk(K),mylk($difference(K,1))) ) ) ).

tff(mylk_tot,axiom,
    $lesseq(mylk(problen),probsize) ).

tff(mysumr_0,axiom,
    ! [D: $real,T: $int,C: $int] : ( mysumr(D,T,C,0) = 0.0 ) ).

tff(mysumr_n,axiom,
    ! [D: $real,T: $int,C: $int,K: $int] :
      ( $lesseq(1,K)
     => ( mysumr(D,T,C,K) = $sum($product(dc(D,T,C),$product(recexp(D,T,K),$to_real(lk(K)))),mysumr(D,T,C,$difference(K,1))) ) ) ).

%------------------------------------------------------------------------------

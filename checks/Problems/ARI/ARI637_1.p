%------------------------------------------------------------------------------
% File     : ARI637_1 : TPTP v9.0.0. Released v6.3.0.
% Domain   : Arithmetic
% Problem  : Example 13
% Version  : Especial.
% English  :

% Refs     : [ALR14] Avigad et al. (2014), A Heuristic Prover for Real Ineq
%          : [LAR14] Lewis et al. (2014), A Heuristic Prover for Real Inequ
%          : [Lew14] Lewis (2014), Email to Geoff Sutcliffe
% Source   : [Lew14]
% Names    : Example 13 [Lew14]

% Status   : Theorem
% Rating   : 0.75 v9.0.0, 0.62 v8.2.0, 0.75 v7.5.0, 0.80 v7.4.0, 0.75 v7.3.0, 0.67 v7.1.0, 0.83 v7.0.0, 1.00 v6.3.0
% Syntax   : Number of formulae    :    7 (   4 unt;   3 typ;   0 def)
%            Number of atoms       :    4 (   1 equ)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    3 (   2 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number arithmetic     :   11 (   3 atm;   3 fun;   3 num;   2 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   3 usr;   4 con; 0-2 aty)
%            Number of variables   :    2 (   2   !;   0   ?;   2   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(a_type,type,
    a: $real ).

tff(b_type,type,
    b: $real ).

tff(f_type,type,
    f: $real > $real ).

tff(f_feature,axiom,
    ! [X: $real,Y: $real] : ( f($sum(X,Y)) = $product(f(X),f(Y)) ) ).

tff(hypothesis,hypothesis,
    $greater(f(a),2.0) ).

tff(hypothesis_01,hypothesis,
    $greater(f(b),2.0) ).

tff(conclusion,conjecture,
    $greater(f($sum(a,b)),4.0) ).

%------------------------------------------------------------------------------

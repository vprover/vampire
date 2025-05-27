%------------------------------------------------------------------------------
% File     : ARI576_1 : TPTP v9.0.0. Released v5.1.0.
% Domain   : Arithmetic
% Problem  : Inequation system is solvable (e.g., X = 10)
% Version  : Especial.
% English  :

% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v7.4.0, 0.17 v7.3.0, 0.38 v7.1.0, 0.17 v6.4.0, 0.00 v6.2.0, 0.40 v6.1.0, 0.44 v6.0.0, 0.50 v5.4.0, 0.25 v5.3.0, 0.29 v5.2.0, 0.40 v5.1.0
% Syntax   : Number of formulae    :    1 (   0 unt;   0 typ;   0 def)
%            Number of atoms       :    2 (   0 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    1 (   0   ~;   0   |;   1   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    3 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number arithmetic     :    9 (   2 atm;   2 fun;   4 num;   1 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   0 usr;   4 con; 0-2 aty)
%            Number of variables   :    1 (   0   !;   1   ?;   1   :)
% SPC      : TF0_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
tff(ineq_sys_solvable_1,conjecture,
    ? [X: $int] :
      ( $lesseq($product(2,X),21)
      & $lesseq(29,$product(3,X)) ) ).

%------------------------------------------------------------------------------

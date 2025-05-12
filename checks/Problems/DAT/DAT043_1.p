%------------------------------------------------------------------------------
% File     : DAT043_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Three different elements
% Version  : [PW06] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (66) [PW06]

% Status   : Theorem
% Rating   : 0.25 v7.5.0, 0.30 v7.4.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.14 v6.4.0, 0.00 v6.3.0, 0.29 v6.2.0, 0.50 v6.1.0, 0.67 v6.0.0, 0.71 v5.5.0, 0.78 v5.4.0, 0.75 v5.3.0, 1.00 v5.0.0
% Syntax   : Number of formulae    :   19 (   4 unt;   6 typ;   0 def)
%            Number of atoms       :   39 (   9 equ)
%            Maximal formula atoms :    6 (   2 avg)
%            Number of connectives :   20 (   5   ~;   1   |;   5   &)
%                                         (   7 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of FOOLs       :   11 (  11 fml;   0 var)
%            Number arithmetic     :   26 (   4 atm;   2 fun;   5 num;  15 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    7 (   4   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    5 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   4 usr;   4 con; 0-2 aty)
%            Number of variables   :   27 (  27   !;   0   ?;  27   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : 
%------------------------------------------------------------------------------
%----Includes axioms for collections with counting
include('Axioms/DAT002_0.ax').
include('Axioms/DAT002=1.ax').
%------------------------------------------------------------------------------
tff(co1,conjecture,
    ! [U: collection,V: $int,W: $int,X: $int] :
      ( ( $greater(V,W)
        & $greater(W,X)
        & in(V,U)
        & in(W,U)
        & in(X,U) )
     => $greater(count(U),2) ) ).

%------------------------------------------------------------------------------

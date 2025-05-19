%------------------------------------------------------------------------------
% File     : DAT023_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Removing 1 and 2 ensures elements are greater than 2
% Version  : [PW06] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (46) [PW06]

% Status   : Theorem
% Rating   : 0.12 v7.5.0, 0.20 v7.4.0, 0.00 v6.3.0, 0.14 v6.2.0, 0.50 v6.1.0, 0.56 v6.0.0, 0.57 v5.5.0, 0.67 v5.4.0, 0.62 v5.3.0, 0.70 v5.2.0, 1.00 v5.0.0
% Syntax   : Number of formulae    :   11 (   3 unt;   5 typ;   0 def)
%            Number of atoms       :   19 (   3 equ)
%            Maximal formula atoms :    5 (   1 avg)
%            Number of connectives :   11 (   3   ~;   1   |;   2   &)
%                                         (   2 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of FOOLs       :    5 (   5 fml;   0 var)
%            Number arithmetic     :   16 (   2 atm;   0 fun;   5 num;   9 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    6 (   3   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    4 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   3 usr;   5 con; 0-2 aty)
%            Number of variables   :   15 (  15   !;   0   ?;  15   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : 
%------------------------------------------------------------------------------
%----Includes axioms for collections
include('Axioms/DAT002_0.ax').
%------------------------------------------------------------------------------
tff(co1,conjecture,
    ! [U: collection,V: collection] :
      ( ( ! [W: $int] :
            ( in(W,V)
           => $greater(W,0) )
        & ( U = remove(4,remove(1,remove(2,V))) ) )
     => ! [X: $int] :
          ( in(X,U)
         => $greater(X,2) ) ) ).

%------------------------------------------------------------------------------

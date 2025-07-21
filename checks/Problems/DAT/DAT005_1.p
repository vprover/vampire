%------------------------------------------------------------------------------
% File     : DAT005_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Element between 33 and 44
% Version  : [PW06] axioms.
% English  :

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (29) [PW06]

% Status   : Theorem
% Rating   : 0.12 v8.2.0, 0.25 v7.5.0, 0.30 v7.4.0, 0.00 v6.3.0, 0.14 v6.2.0, 0.50 v6.1.0, 0.56 v6.0.0, 0.57 v5.5.0, 0.56 v5.4.0, 0.62 v5.3.0, 0.70 v5.2.0, 0.83 v5.1.0, 0.80 v5.0.0
% Syntax   : Number of formulae    :    6 (   1 unt;   3 typ;   0 def)
%            Number of atoms       :   19 (   4 equ)
%            Maximal formula atoms :    5 (   3 avg)
%            Number of connectives :    5 (   0   ~;   1   |;   3   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   6 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of FOOLs       :   11 (  11 fml;   0 var)
%            Number arithmetic     :   22 (   4 atm;   0 fun;  12 num;   6 var)
%            Number of types       :    2 (   1 usr;   1 ari)
%            Number of type conns  :    5 (   2   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    4 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    9 (   2 usr;   7 con; 0-3 aty)
%            Number of variables   :   10 (  10   !;   0   ?;  10   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
%----Includes axioms for arrays
include('Axioms/DAT001_0.ax').
%------------------------------------------------------------------------------
tff(co1,conjecture,
    ! [U: array,V: array,W: $int] :
      ( ( ( U = write(write(write(write(V,3,33),4,444),5,55),4,44) )
        & $lesseq(3,W)
        & $lesseq(W,4) )
     => ( $lesseq(33,read(U,W))
        & $lesseq(read(U,W),44) ) ) ).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : DAT042_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Some collection has 3 as an element
% Version  : [PW06] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (65) [PW06]

% Status   : Theorem
% Rating   : 0.50 v9.0.0, 0.38 v8.2.0, 0.12 v7.5.0, 0.30 v7.4.0, 0.12 v7.3.0, 0.17 v7.1.0, 0.33 v7.0.0, 0.14 v6.4.0, 0.67 v6.3.0, 0.43 v6.2.0, 0.75 v6.1.0, 0.89 v6.0.0, 0.86 v5.5.0, 0.78 v5.4.0, 0.75 v5.3.0, 0.70 v5.2.0, 0.67 v5.1.0, 0.60 v5.0.0
% Syntax   : Number of formulae    :   19 (   5 unt;   6 typ;   0 def)
%            Number of atoms       :   34 (  10 equ)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   15 (   5   ~;   1   |;   1   &)
%                                         (   7 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of FOOLs       :   11 (  11 fml;   0 var)
%            Number arithmetic     :   20 (   1 atm;   2 fun;   5 num;  12 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    7 (   4   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    4 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   4 usr;   4 con; 0-2 aty)
%            Number of variables   :   24 (  23   !;   1   ?;  24   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : 
%------------------------------------------------------------------------------
%----Includes axioms for collections with counting
include('Axioms/DAT002_0.ax').
include('Axioms/DAT002=1.ax').
%------------------------------------------------------------------------------
tff(co1,conjecture,
    ? [U: collection] : ( count(U) = 3 ) ).

%------------------------------------------------------------------------------

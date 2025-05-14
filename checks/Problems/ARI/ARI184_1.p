%--------------------------------------------------------------------------
% File     : ARI184_1 : TPTP v9.0.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Integer: Monotonic function formula 2
% Version  : Especial.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (19) [PW06]

% Status   : Theorem
% Rating   : 0.60 v9.0.0, 0.50 v7.5.0, 0.40 v7.4.0, 0.17 v7.3.0, 0.25 v7.1.0, 0.17 v7.0.0, 0.33 v6.4.0, 0.67 v6.3.0, 0.50 v6.2.0, 0.80 v6.1.0, 0.89 v6.0.0, 0.88 v5.4.0, 1.00 v5.3.0, 0.86 v5.2.0, 0.80 v5.1.0, 0.75 v5.0.0
% Syntax   : Number of formulae    :    2 (   0 unt;   1 typ;   0 def)
%            Number of atoms       :    3 (   0 equ)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   5 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number arithmetic     :   10 (   3 atm;   2 fun;   2 num;   3 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   1 usr;   2 con; 0-2 aty)
%            Number of variables   :    3 (   3   !;   0   ?;   3   :)
% SPC      : TF0_THM_NEQ_ARI

% Comments : 
%--------------------------------------------------------------------------
tff(f_type,type,
    f: $int > $int ).

tff(co1,conjecture,
    ( ! [U: $int,V: $int] :
        ( $less(U,V)
       => $less(f(U),f(V)) )
   => ! [W: $int] : $greater(f($sum(f(W),2)),$sum(f(f(W)),1)) ) ).

%--------------------------------------------------------------------------

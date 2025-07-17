%------------------------------------------------------------------------------
% File     : ARI700_1 : TPTP v9.0.0. Released v6.3.0.
% Domain   : Arithmetic
% Problem  : Solve a simple system of nonlinear equations
% Version  : Especial.
% English  :

% Refs     : [BHS07] Beckert et al. (2007), Verification of Object-Oriented
%          : [Rue14] Ruemmer (2014), Email to Geoff Sutcliffe
% Source   : [Rue14]
% Names    : simplify23.pri [BHS07]
%          : poly_simplify23.p [Rue14]

% Status   : Theorem
% Rating   : 0.38 v8.2.0, 0.50 v8.1.0, 0.38 v7.5.0, 0.40 v7.4.0, 0.38 v7.3.0, 0.33 v7.0.0, 0.43 v6.4.0, 0.33 v6.3.0
% Syntax   : Number of formulae    :    7 (   3 unt;   4 typ;   0 def)
%            Number of atoms       :    3 (   3 equ)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number arithmetic     :   17 (   0 atm;  11 fun;   6 num;   0 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   10 (   4 usr;   9 con; 0-2 aty)
%            Number of variables   :    0 (   0   !;   0   ?;   0   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : KeY arithmetic regression test, http://www.key-project.org
%------------------------------------------------------------------------------
tff(y_type,type,
    y: $int ).

tff(a_type,type,
    a: $int ).

tff(x_type,type,
    x: $int ).

tff(b_type,type,
    b: $int ).

tff(eq1,axiom,
    $product($product(98164184,y),y) = a ).

tff(eq2,axiom,
    $product($product(6472,x),y) = b ).

tff(conj,conjecture,
    $product(5235848,$product($product($product(123,x),x),a)) = $product(12270523,$product($product(123,b),b)) ).

%------------------------------------------------------------------------------

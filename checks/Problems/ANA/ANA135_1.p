%------------------------------------------------------------------------------
% File     : ANA135_1 : TPTP v9.0.0. Released v8.2.0.
% Domain   : Number theory
% Problem  : const_mul_lim_14_100_x
% Version  : Especial.
% English  : lim(14/100 f(x)) = 14/100 lim(f(x))

% Refs     : [Sch22] Schoisswohl (2022), Email to G. Sutcliffe
%          : [KK+23] Korovin et al. (2023), ALASCA: Reasoning in Quantified
% Source   : [Sch22]
% Names    : const_mul_lim_14_100_x.smt2 [Sch22]

% Status   : Theorem
% Rating   : 0.75 v8.2.0
% Syntax   : Number of formulae    :    5 (   0 unt;   3 typ;   0 def)
%            Number of atoms       :   22 (   2 equ)
%            Maximal formula atoms :   11 (  11 avg)
%            Number of connectives :   26 (   6   ~;   0   |;   8   &)
%                                         (   0 <=>;  12  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   11 (  11 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number arithmetic     :   90 (  20 atm;  36 fun;  28 num;   6 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    3 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   10 (   3 usr;   5 con; 0-2 aty)
%            Number of variables   :    6 (   4   !;   2   ?;   6   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Translated from SMT UFLRA by SMTtoTPTP.
%------------------------------------------------------------------------------
%% Declarations:
tff(f,type,
    f: $real > $real ).

tff(a,type,
    a: $real ).

tff(l,type,
    l: $real ).

%% Assertions:
%% ∀ epsilon:Real ((0.0 < epsilon) ⇒ ∃ delta:Real ((0.0 < delta) ∧ ∀ x:Real ((¬(x = a) ∧ ((if ((x - a) ≥ 0.0) (x - a) else -(x - a)) < delta)) ⇒ ((if ((f(x) - l) ≥ 0.0) (f(x) - l) else -(f(x) - l)) < epsilon))))
tff(formula_1,axiom,
    ! [Epsilon: $real] :
      ( $less(0.0,Epsilon)
     => ? [Delta: $real] :
          ( $less(0.0,Delta)
          & ! [X: $real] :
              ( ( ( X != a )
                & ( $greatereq($difference(X,a),0.0)
                 => $less($difference(X,a),Delta) )
                & ( ~ $greatereq($difference(X,a),0.0)
                 => $less($uminus($difference(X,a)),Delta) ) )
             => ( ( $greatereq($difference(f(X),l),0.0)
                 => $less($difference(f(X),l),Epsilon) )
                & ( ~ $greatereq($difference(f(X),l),0.0)
                 => $less($uminus($difference(f(X),l)),Epsilon) ) ) ) ) ) ).

%% ∀ epsilon:Real ((0.0 < epsilon) ⇒ ∃ delta:Real ((0.0 < delta) ∧ ∀ x:Real ((¬(x = a) ∧ ((if ((x - a) ≥ 0.0) (x - a) else -(x - a)) < delta)) ⇒ ((if ((((14.0 / 100.0) * f(x)) - ((14.0 / 100.0) * l)) ≥ 0.0) (((14.0 / 100.0) * f(x)) - ((14.0 / 100.0) * l)) else -(((14.0 / 100.0) * f(x)) - ((14.0 / 100.0) * l))) < epsilon))))
tff(formula_2,conjecture,
    ! [Epsilon: $real] :
      ( $less(0.0,Epsilon)
     => ? [Delta: $real] :
          ( $less(0.0,Delta)
          & ! [X: $real] :
              ( ( ( X != a )
                & ( $greatereq($difference(X,a),0.0)
                 => $less($difference(X,a),Delta) )
                & ( ~ $greatereq($difference(X,a),0.0)
                 => $less($uminus($difference(X,a)),Delta) ) )
             => ( ( $greatereq($difference($product($quotient(14.0,100.0),f(X)),$product($quotient(14.0,100.0),l)),0.0)
                 => $less($difference($product($quotient(14.0,100.0),f(X)),$product($quotient(14.0,100.0),l)),Epsilon) )
                & ( ~ $greatereq($difference($product($quotient(14.0,100.0),f(X)),$product($quotient(14.0,100.0),l)),0.0)
                 => $less($uminus($difference($product($quotient(14.0,100.0),f(X)),$product($quotient(14.0,100.0),l))),Epsilon) ) ) ) ) ) ).

%------------------------------------------------------------------------------

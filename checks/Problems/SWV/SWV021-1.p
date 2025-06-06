%--------------------------------------------------------------------------
% File     : SWV021-1 : TPTP v8.2.0. Released v2.7.0.
% Domain   : Software Verification
% Problem  : Show that the add function is commutative.
% Version  : [Cla03] axioms : Especial.
% English  : A proof obligation formulated as a satisfiability problem.
%            Given the definition of "add" on successor-naturals, show
%            that no two terms t1 and t2 can be found such that
%            add(t1,t2) /= add(t2,t1). In other words, show that adding
%            the negation of that as a clause is still consistent.

% Refs     : [Cla03] Claessen (2003), Email to G. Sutcliffe
% Source   : [Cla03]
% Names    :

% Status   : Satisfiable
% Rating   : 0.60 v8.2.0, 0.70 v8.1.0, 0.88 v7.5.0, 0.89 v7.4.0, 0.91 v7.3.0, 0.89 v7.1.0, 0.88 v7.0.0, 0.86 v6.3.0, 0.88 v6.2.0, 0.90 v6.1.0, 0.89 v6.0.0, 0.86 v5.5.0, 0.88 v5.4.0, 0.90 v5.3.0, 0.89 v5.2.0, 0.90 v5.0.0, 0.89 v4.1.0, 0.86 v4.0.1, 0.80 v4.0.0, 0.75 v3.7.0, 0.67 v3.5.0, 1.00 v3.4.0, 0.75 v3.3.0, 0.67 v3.2.0, 0.80 v3.1.0, 0.67 v2.7.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   6 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    8 (   1 sgn)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments : Infinox says this has no finite (counter-) models.
%--------------------------------------------------------------------------
cnf(zero_is_not_s,axiom,
    n0 != s(X) ).

cnf(successor_is_injective,axiom,
    ( s(X) != s(Y)
    | X = Y ) ).

cnf(definition_add_0,axiom,
    add(n0,Y) = Y ).

cnf(definition_add_s,axiom,
    add(s(X),Y) = s(add(X,Y)) ).

cnf(consistency_of_add_commutative,negated_conjecture,
    add(X,Y) = add(Y,X) ).

%--------------------------------------------------------------------------

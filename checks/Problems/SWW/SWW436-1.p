%------------------------------------------------------------------------------
% File     : SWW436-1 : TPTP v8.2.0. Released v5.2.0.
% Domain   : Software Verification
% Problem  : Randomly generated entailment of the form F -> \bot (n = 15)
% Version  : Especial.
% English  : A randomly generated entailment with n program variables.
%            Negated equalities and list segments are added at random, with
%            specific paramenters so that about half of the generated
%            entailments are valid (or, equivalently, F is unsatisfiable).
%            Normalization and well-formedness axioms should be enough to
%            decide these entailments.

% Refs     : [RN11]  Rybalchenko & Navarro Perez (2011), Separation Logic +
%          : [Nav11] Navarro Perez (2011), Email to Geoff Sutcliffe
% Source   : [Nav11]
% Names    : spaguetti-15-e02 [Nav11]

% Status   : Unsatisfiable
% Rating   : 0.60 v8.2.0, 0.67 v8.1.0, 0.58 v7.5.0, 0.68 v7.4.0, 0.65 v7.3.0, 0.58 v7.1.0, 0.50 v7.0.0, 0.60 v6.3.0, 0.45 v6.2.0, 0.60 v6.1.0, 0.71 v6.0.0, 0.80 v5.5.0, 0.95 v5.3.0, 0.94 v5.2.0
% Syntax   : Number of clauses     :   21 (  13 unt;   3 nHn;  19 RR)
%            Number of literals    :   32 (  17 equ;  18 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :   18 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :   19 (  19 usr;  16 con; 0-2 aty)
%            Number of variables   :   38 (   9 sgn)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%------------------------------------------------------------------------------
%----Include axioms for Lists in Separation Logic
include('Axioms/SWV013-0.ax').
%------------------------------------------------------------------------------
cnf(premise_1,hypothesis,
    x6 != x14 ).

cnf(premise_2,hypothesis,
    x3 != x6 ).

cnf(premise_3,hypothesis,
    x3 != x13 ).

cnf(premise_4,hypothesis,
    x4 != x6 ).

cnf(premise_5,hypothesis,
    x4 != x7 ).

cnf(premise_6,hypothesis,
    x4 != x12 ).

cnf(premise_7,hypothesis,
    x1 != x3 ).

cnf(premise_8,hypothesis,
    x10 != x15 ).

cnf(premise_9,hypothesis,
    heap(sep(lseg(x13,x2),sep(lseg(x4,x9),sep(lseg(x4,x13),sep(lseg(x1,x5),sep(lseg(x1,x6),sep(lseg(x8,x14),sep(lseg(x8,x15),sep(lseg(x8,x1),sep(lseg(x14,x8),sep(lseg(x15,x4),sep(lseg(x2,x15),sep(lseg(x2,x9),sep(lseg(x9,x7),sep(lseg(x9,x6),sep(lseg(x3,x10),sep(lseg(x6,x2),emp))))))))))))))))) ).

cnf(conclusion_1,negated_conjecture,
    ( x1 = x1
    | ~ heap(emp) ) ).

%------------------------------------------------------------------------------

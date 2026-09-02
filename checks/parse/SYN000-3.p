%------------------------------------------------------------------------------
% File     : SYN000-3 : TPTP v9.3.1. Bugfixed v9.3.0.
% Domain   : Syntactic
% Problem  : Typed TPTP CNF syntax
% Version  : Biased.
% English  : 

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : ? v9.3.0
% Syntax   : Number of clauses     :    8 (   2 unt;   6 nHn;   0 RR)
%            Number of literals    :   54 (   3 equ;   8 neg)
%            Maximal clause size   :    5 (   6 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of types       :    1 (   0 usr)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :   21 (  18 usr;  12 prp; 0-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   11 (   0 sgn  11   !;   0   ?;  11   :)
% SPC      : UNK

% Comments :
% Bugfixes : v9.3.0 - Removed surplus ()s around equalities
%------------------------------------------------------------------------------
%----Propositional
tcf(propositional,axiom,
    ( p0
    | ~ q0
    | r0
    | ~ s0 ) ).

%----First-order
tcf(first_order_tcf,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( p(X)
      | ~ q(X,a)
      | r(X,f(Y),g(X,f(Y),Z))
      | ~ s(f(f(f(b)))) ) ).

%----Equality
tcf(equality,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( f(Y) = g(X,f(Y),Z)
      | f(f(f(b))) != a
      | X = f(Y) ) ).

%----True and false
tcf(true_false,axiom,
    ( $true
    | $false ) ).

%----Quoted symbols
tcf(single_quoted,axiom,
    ! [Y: $i] :
      ( 'A proposition'
      | 'A predicate'(Y)
      | p('A constant')
      | p('A function'(a))
      | p('A \'quoted \\ escape\'') ) ).

%----Connectives - seen them all already

%----Annotated formula names
tcf(123,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( p(X)
      | ~ q(X,a)
      | r(X,f(Y),g(X,f(Y),Z))
      | ~ s(f(f(f(b)))) ) ).

%----Roles - seen axiom already
tcf(role_hypothesis,hypothesis,
    p(h) ).

tcf(role_negated_conjecture,negated_conjecture,
    ! [X: $i] : ~ p(X) ).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : PUZ001+1 : TPTP v7.3.0. Released v2.0.0.
% Domain   : Puzzles
% Problem  : Dreadbury Mansion
% Version  : Especial.
%            Theorem formulation : Reduced > Complete.
% English  : Someone who lives in Dreadbury Mansion killed Aunt Agatha.
%            Agatha, the butler, and Charles live in Dreadbury Mansion,
%            and are the only people who live therein. A killer always
%            hates his victim, and is never richer than his victim.
%            Charles hates no one that Aunt Agatha hates. Agatha hates
%            everyone except the butler. The butler hates everyone not
%            richer than Aunt Agatha. The butler hates everyone Aunt
%            Agatha hates. No one hates everyone. Agatha is not the
%            butler. Therefore : Agatha killed herself.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Hah94] Haehnle (1994), Email to G. Sutcliffe
% Source   : [Hah94]
% Names    : Pelletier 55 [Pel86]

% Status   : Theorem
% Rating   : 0.07 v7.2.0, 0.03 v7.1.0, 0.04 v7.0.0, 0.07 v6.4.0, 0.12 v6.3.0, 0.04 v6.2.0, 0.12 v6.1.0, 0.20 v6.0.0, 0.26 v5.5.0, 0.07 v5.3.0, 0.19 v5.2.0, 0.00 v5.0.0, 0.08 v4.1.0, 0.13 v4.0.0, 0.12 v3.7.0, 0.14 v3.5.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.11 v3.2.0, 0.22 v3.1.0, 0.17 v2.7.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
% Syntax   : Number of formulae    :   14 (   6 unit)
%            Number of atoms       :   24 (   5 equality)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :   16 (   6   ~;   2   |;   1   &)
%                                         (   0 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   3 constant; 0-0 arity)
%            Number of variables   :   12 (   0 sgn;  10   !;   2   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Modified by Geoff Sutcliffe.
%          : Also known as "Who killed Aunt Agatha"
%------------------------------------------------------------------------------
%----Problem axioms
fof(pel55_1,axiom,
    ( ? [X] :
        ( lives(X)
        & killed(X,agatha) ) )).

fof(pel55_2_1,axiom,
    ( lives(agatha) )).

fof(pel55_2_2,axiom,
    ( lives(butler) )).

fof(pel55_2_3,axiom,
    ( lives(charles) )).

fof(pel55_3,axiom,
    ( ! [X] :
        ( lives(X)
       => ( X = agatha
          | X = butler
          | X = charles ) ) )).

fof(pel55_4,axiom,
    ( ! [X,Y] :
        ( killed(X,Y)
       => hates(X,Y) ) )).

fof(pel55_5,axiom,
    ( ! [X,Y] :
        ( killed(X,Y)
       => ~ richer(X,Y) ) )).

fof(pel55_6,axiom,
    ( ! [X] :
        ( hates(agatha,X)
       => ~ hates(charles,X) ) )).

fof(pel55_7,axiom,
    ( ! [X] :
        ( X != butler
       => hates(agatha,X) ) )).

fof(pel55_8,axiom,
    ( ! [X] :
        ( ~ richer(X,agatha)
       => hates(butler,X) ) )).

fof(pel55_9,axiom,
    ( ! [X] :
        ( hates(agatha,X)
       => hates(butler,X) ) )).

fof(pel55_10,axiom,
    ( ! [X] :
      ? [Y] : ~ hates(X,Y) )).

fof(pel55_11,axiom,
    (  agatha != butler )).

fof(pel55,conjecture,
    ( killed(agatha,agatha) )).

%------------------------------------------------------------------------------

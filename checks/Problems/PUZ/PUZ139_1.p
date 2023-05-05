%------------------------------------------------------------------------------
% File     : PUZ139_1 : TPTP v8.1.2. Released v6.1.0.
% Domain   : Puzzles
% Problem  : Caramel vanilla coffee helps people stay awake
% Version  : Especial.
% English  :

% Refs     : [Arh14] Arhami (2010), Email to Geoff Sutcliffe
% Source   : [Arh14]
% Names    : 

% Status   : Theorem
% Rating   : 0.00 v6.4.0
% Syntax   : Number of formulae    :    9 (   2 unt;   7 typ;   0 def)
%            Number of atoms       :    2 (   0 equ)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of types       :    3 (   2 usr)
%            Number of type conns  :    3 (   2   >;   1   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-3 aty)
%            Number of variables   :    2 (   1   !;   0   ?;   2   :)
%                                         (   1  !>;   0  ?*;   0  @-;   0  @+)
% SPC      : TF1_THM_NEQ_NAR

% Comments : 
%------------------------------------------------------------------------------
tff(beverage_type,type,
    beverage: $tType ).

tff(syrup_type,type,
    syrup: $tType ).

%----Coffee is a beverage
tff(coffee_type,type,
    coffee: beverage ).

%----Vanilla syrup is a syrup
tff(vanilla_syrup_type,type,
    vanilla_syrup: syrup ).

%----Caramel syrup is a syrup
tff(caramel_syrup_type,type,
    caramel_syrup: syrup ).

%----The mixture of a syrup and a beverage is a beverage
%----The mixture of a syrup and a syrup is a syrup
tff(mixture_type,type,
    mixture: 
      !>[BeverageOrSyrup: $tType] : ( ( BeverageOrSyrup * syrup ) > BeverageOrSyrup ) ).

%----The mixture of coffee and any syrup helps people stay awake
tff(help_people_stay_awake_type,type,
    help_people_stay_awake: beverage > $o ).

tff(mixture_of_coffee_help_people_stay_awake,axiom,
    ! [S: syrup] : help_people_stay_awake(mixture(beverage,coffee,S)) ).

%----Caramel vanilla coffee help people stay awake
tff(caramel_vanilla_coffee_help_people_stay_awake,conjecture,
    help_people_stay_awake(mixture(beverage,coffee,mixture(syrup,caramel_syrup,vanilla_syrup))) ).

%------------------------------------------------------------------------------

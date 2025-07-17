%------------------------------------------------------------------------------
% File     : ITP001_1 : TPTP v9.0.0. Released v8.1.0.
% Domain   : Interactive Theorem Proving
% Problem  : SMT-LIB Gauss_Jordan Rref 00241_010989
% Version  : [Des21] axioms.
% English  :

% Refs     : [Des21] Desharnais (2021), Email to Geoff Sutcliffe
% Source   : [Des21]
% Names    : Gauss_Jordan-0017_Rref-prob_00241_010989 [Des21]

% Status   : Theorem
% Rating   : 0.75 v8.2.0, 1.00 v8.1.0
% Syntax   : Number of formulae    :  859 ( 167 unt; 199 typ;   0 def)
%            Number of atoms       : 1782 ( 561 equ)
%            Maximal formula atoms :   13 (   2 avg)
%            Number of connectives : 1368 ( 246   ~;  22   |; 367   &)
%                                         ( 235 <=>; 498  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   14 (   5 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number arithmetic     : 1650 ( 426 atm; 387 fun; 430 num; 407 var)
%            Number of types       :   54 (  52 usr;   1 ari)
%            Number of type conns  :  191 ( 116   >;  75   *;   0   +;   0  <<)
%            Number of predicates  :   36 (  31 usr;   2 prp; 0-3 aty)
%            Number of functors    :  120 ( 116 usr;  33 con; 0-2 aty)
%            Number of variables   : 1586 (1534   !;  52   ?;1586   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Translated from SMT format using smttotptp 0.9.10. See
%            https://bitbucket.org/peba123/smttotptp/src/master/
%          : SMT-LIB AUFLIA logic
%------------------------------------------------------------------------------
%% Types:
tff('C_nat_fun$',type,
    'C_nat_fun$': $tType ).

tff('Int_bool_fun$',type,
    'Int_bool_fun$': $tType ).

tff('Nat_b_vec_b_vec$',type,
    'Nat_b_vec_b_vec$': $tType ).

tff('Int_c_fun$',type,
    'Int_c_fun$': $tType ).

tff('Nat_nat_bool_fun_fun$',type,
    'Nat_nat_bool_fun_fun$': $tType ).

tff('B_b_fun$',type,
    'B_b_fun$': $tType ).

tff('C_a_b_vec_bool_fun_fun$',type,
    'C_a_b_vec_bool_fun_fun$': $tType ).

tff('A_b_vec_b_vec_b_vec$',type,
    'A_b_vec_b_vec_b_vec$': $tType ).

tff('C_c_fun$',type,
    'C_c_fun$': $tType ).

tff('Int_b_vec_b_vec$',type,
    'Int_b_vec_b_vec$': $tType ).

tff('Int_b_fun$',type,
    'Int_b_fun$': $tType ).

tff('Int_set$',type,
    'Int_set$': $tType ).

tff('Int_int_fun$',type,
    'Int_int_fun$': $tType ).

tff('A_b_vec_b_vec$',type,
    'A_b_vec_b_vec$': $tType ).

tff('B$',type,
    'B$': $tType ).

tff('A_b_vec_c_vec$',type,
    'A_b_vec_c_vec$': $tType ).

tff('Num_bool_fun$',type,
    'Num_bool_fun$': $tType ).

tff('A_b_vec_c_vec_b_vec_b_vec$',type,
    'A_b_vec_c_vec_b_vec_b_vec$': $tType ).

tff('C_a_b_vec_fun$',type,
    'C_a_b_vec_fun$': $tType ).

tff('Int_b_vec_c_vec$',type,
    'Int_b_vec_c_vec$': $tType ).

tff('B_nat_fun$',type,
    'B_nat_fun$': $tType ).

tff('Nat_nat_fun$',type,
    'Nat_nat_fun$': $tType ).

tff('Int_nat_fun$',type,
    'Int_nat_fun$': $tType ).

tff('C$',type,
    'C$': $tType ).

tff('A_b_vec_b_vec_c_vec$',type,
    'A_b_vec_b_vec_c_vec$': $tType ).

tff('Nat$',type,
    'Nat$': $tType ).

tff('B_int_fun$',type,
    'B_int_fun$': $tType ).

tff('C_b_fun$',type,
    'C_b_fun$': $tType ).

tff('A_b_vec$',type,
    'A_b_vec$': $tType ).

tff('C_int_fun$',type,
    'C_int_fun$': $tType ).

tff('B_a_fun$',type,
    'B_a_fun$': $tType ).

tff('Num$',type,
    'Num$': $tType ).

tff('Nat_b_vec_c_vec$',type,
    'Nat_b_vec_c_vec$': $tType ).

tff('Nat_b_vec$',type,
    'Nat_b_vec$': $tType ).

tff('Num_set$',type,
    'Num_set$': $tType ).

tff(tlbool,type,
    tlbool: $tType ).

tff('A_b_vec_c_vec_b_vec$',type,
    'A_b_vec_c_vec_b_vec$': $tType ).

tff('A_bool_fun$',type,
    'A_bool_fun$': $tType ).

tff('B_b_bool_fun_fun$',type,
    'B_b_bool_fun_fun$': $tType ).

tff('A$',type,
    'A$': $tType ).

tff('Nat_b_fun$',type,
    'Nat_b_fun$': $tType ).

tff('A_a_fun$',type,
    'A_a_fun$': $tType ).

tff('Int_int_bool_fun_fun$',type,
    'Int_int_bool_fun_fun$': $tType ).

tff('Int_b_vec$',type,
    'Int_b_vec$': $tType ).

tff('A_b_vec_bool_fun$',type,
    'A_b_vec_bool_fun$': $tType ).

tff('Nat_bool_fun$',type,
    'Nat_bool_fun$': $tType ).

tff('Nat_set$',type,
    'Nat_set$': $tType ).

tff('B_c_fun$',type,
    'B_c_fun$': $tType ).

tff('Nat_int_fun$',type,
    'Nat_int_fun$': $tType ).

tff('B_a_bool_fun_fun$',type,
    'B_a_bool_fun_fun$': $tType ).

tff('A_b_vec_c_vec_b_vec_c_vec$',type,
    'A_b_vec_c_vec_b_vec_c_vec$': $tType ).

tff('B_bool_fun$',type,
    'B_bool_fun$': $tType ).

%% Declarations:
tff('less$a',type,
    'less$a': 'B_b_bool_fun_fun$' ).

tff('vec_nth$m',type,
    'vec_nth$m': ( 'Int_b_vec_b_vec$' * 'B$' ) > 'Int_b_vec$' ).

tff('fun_app$o',type,
    'fun_app$o': ( 'B_int_fun$' * 'B$' ) > $int ).

tff('reduced_row_echelon_form$',type,
    'reduced_row_echelon_form$': 'A_b_vec_c_vec$' > $o ).

tff('fun_app$ab',type,
    'fun_app$ab': ( 'Nat_b_fun$' * 'Nat$' ) > 'B$' ).

tff('dbl_inc$',type,
    'dbl_inc$': 'Int_int_fun$' ).

tff('fun_app$y',type,
    'fun_app$y': ( 'C_b_fun$' * 'C$' ) > 'B$' ).

tff('reduced_row_echelon_form$a',type,
    'reduced_row_echelon_form$a': 'Int_b_vec_c_vec$' > $o ).

tff('vec_nth$f',type,
    'vec_nth$f': ( 'A_b_vec_b_vec_c_vec$' * 'C$' ) > 'A_b_vec_b_vec$' ).

tff('is_zero_row$i',type,
    'is_zero_row$i': ( 'B$' * 'A_b_vec_b_vec$' ) > $o ).

tff('uuc$',type,
    'uuc$': ( 'Int_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('zero$e',type,
    'zero$e': 'Int_set$' ).

tff('uua$',type,
    'uua$': ( 'A_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('uub$',type,
    'uub$': ( 'Int_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('vec_nth$l',type,
    'vec_nth$l': ( 'Int_b_vec_c_vec$' * 'C$' ) > 'Int_b_vec$' ).

tff('uuj$',type,
    'uuj$': 'Int_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('uur$',type,
    'uur$': 'A_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('fun_app$l',type,
    'fun_app$l': ( 'B_b_bool_fun_fun$' * 'B$' ) > 'B_bool_fun$' ).

tff('triangle$',type,
    'triangle$': 'Nat_nat_fun$' ).

tff('uuh$',type,
    'uuh$': ( 'Nat_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('uu$',type,
    'uu$': 'C$' > 'B_bool_fun$' ).

tff('is_zero_row$a',type,
    'is_zero_row$a': ( 'C$' * 'Int_b_vec_c_vec$' ) > $o ).

tff('fun_app$u',type,
    'fun_app$u': ( 'Nat_nat_bool_fun_fun$' * 'Nat$' ) > 'Nat_bool_fun$' ).

tff('plus$f',type,
    'plus$f': ( 'Num_set$' * 'Num_set$' ) > 'Num_set$' ).

tff('fun_app$t',type,
    'fun_app$t': ( 'C_a_b_vec_bool_fun_fun$' * 'C$' ) > 'A_b_vec_bool_fun$' ).

tff('member$a',type,
    'member$a': ( 'Nat$' * 'Nat_set$' ) > $o ).

tff('uuo$',type,
    'uuo$': 'A_b_vec_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('vec_nth$b',type,
    'vec_nth$b': ( 'A_b_vec_c_vec_b_vec$' * 'B$' ) > 'A_b_vec_c_vec$' ).

tff('fun_app$a',type,
    'fun_app$a': ( 'Int_int_fun$' * $int ) > $int ).

tff('least$a',type,
    'least$a': 'Nat_bool_fun$' > 'Nat$' ).

tff('fun_app$e',type,
    'fun_app$e': ( 'Nat_bool_fun$' * 'Nat$' ) > $o ).

tff('axis$a',type,
    'axis$a': ( 'B$' * 'A$' ) > 'A_b_vec$' ).

tff('is_zero_row_upt_k$',type,
    'is_zero_row_upt_k$': ( 'C$' * 'Nat$' * 'A_b_vec_c_vec$' ) > $o ).

tff('fun_app$g',type,
    'fun_app$g': ( 'Nat_int_fun$' * 'Nat$' ) > $int ).

tff('is_zero_row$d',type,
    'is_zero_row$d': ( 'C$' * 'Nat_b_vec_c_vec$' ) > $o ).

tff('from_nat$',type,
    'from_nat$': 'Nat_b_fun$' ).

tff('of_nat$a',type,
    'of_nat$a': 'Nat_nat_fun$' ).

tff('nat$',type,
    'nat$': 'Int_nat_fun$' ).

tff('one$c',type,
    'one$c': 'A$' ).

tff('uux$',type,
    'uux$': 'Int_int_bool_fun_fun$' ).

tff('fun_app$q',type,
    'fun_app$q': ( 'A_bool_fun$' * 'A$' ) > $o ).

tff('is_zero_row$g',type,
    'is_zero_row$g': ( 'B$' * 'A_b_vec_b_vec_b_vec$' ) > $o ).

tff('fun_app$v',type,
    'fun_app$v': ( 'Int_c_fun$' * $int ) > 'C$' ).

tff('fun_app$z',type,
    'fun_app$z': ( 'C_nat_fun$' * 'C$' ) > 'Nat$' ).

tff('of_nat$',type,
    'of_nat$': 'Nat_int_fun$' ).

tff('less$',type,
    'less$': ( 'C$' * 'C$' ) > $o ).

tff('reduced_row_echelon_form$g',type,
    'reduced_row_echelon_form$g': 'A_b_vec_b_vec_b_vec$' > $o ).

tff('uum$',type,
    'uum$': 'A_b_vec_c_vec_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('fun_app$f',type,
    'fun_app$f': ( 'Int_nat_fun$' * $int ) > 'Nat$' ).

tff('uuz$',type,
    'uuz$': 'Nat_nat_fun$' ).

tff('plus$d',type,
    'plus$d': ( 'Int_set$' * 'Int_set$' ) > 'Int_set$' ).

tff('fun_app$s',type,
    'fun_app$s': ( 'A_b_vec_bool_fun$' * 'A_b_vec$' ) > $o ).

tff('of_int$',type,
    'of_int$': 'Int_int_fun$' ).

tff('axis$',type,
    'axis$': ( 'C$' * 'A_b_vec$' ) > 'A_b_vec_c_vec$' ).

tff('to_nat$',type,
    'to_nat$': 'B_nat_fun$' ).

tff('fun_app$i',type,
    'fun_app$i': ( 'B_a_fun$' * 'B$' ) > 'A$' ).

tff('reduced_row_echelon_form$h',type,
    'reduced_row_echelon_form$h': 'Nat_b_vec_b_vec$' > $o ).

tff('fun_app$h',type,
    'fun_app$h': ( 'B_bool_fun$' * 'B$' ) > $o ).

tff('reduced_row_echelon_form$f',type,
    'reduced_row_echelon_form$f': 'A_b_vec_c_vec_b_vec_b_vec$' > $o ).

tff(tltrue,type,
    tltrue: tlbool ).

tff('plus$',type,
    'plus$': 'Nat$' > 'Nat_nat_fun$' ).

tff('map_matrix$',type,
    'map_matrix$': ( 'A_a_fun$' * 'A_b_vec_c_vec$' ) > 'A_b_vec_c_vec$' ).

tff('one$b',type,
    'one$b': 'B$' ).

tff('uva$',type,
    'uva$': 'Int_int_fun$' ).

tff('one$',type,
    'one$': 'Nat$' ).

tff('uug$',type,
    'uug$': ( 'A_b_vec_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('uup$',type,
    'uup$': 'Nat_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('fun_app$x',type,
    'fun_app$x': ( 'C_int_fun$' * 'C$' ) > $int ).

tff('fun_app$aa',type,
    'fun_app$aa': ( 'B_c_fun$' * 'B$' ) > 'C$' ).

tff('uul$',type,
    'uul$': 'A_b_vec_c_vec_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('is_zero_row$b',type,
    'is_zero_row$b': ( 'C$' * 'A_b_vec_c_vec_b_vec_c_vec$' ) > $o ).

tff('uun$',type,
    'uun$': 'A_b_vec_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('collect$',type,
    'collect$': 'Nat_bool_fun$' > 'Nat_set$' ).

tff('least$',type,
    'least$': 'B_bool_fun$' > 'B$' ).

tff('vec_nth$j',type,
    'vec_nth$j': ( 'Nat_b_vec_b_vec$' * 'B$' ) > 'Nat_b_vec$' ).

tff('plus$b',type,
    'plus$b': 'B$' > 'B_b_fun$' ).

tff('ncols$',type,
    'ncols$': 'A_b_vec_c_vec$' > 'Nat$' ).

tff('fun_app$j',type,
    'fun_app$j': ( 'C_a_b_vec_fun$' * 'C$' ) > 'A_b_vec$' ).

tff('of_nat_aux$a',type,
    'of_nat_aux$a': ( 'Int_int_fun$' * 'Nat$' ) > 'Int_int_fun$' ).

tff('uui$',type,
    'uui$': ( 'Nat_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('uut$',type,
    'uut$': ( 'A_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('zero$a',type,
    'zero$a': 'A_b_vec_c_vec$' ).

tff('is_zero_row$f',type,
    'is_zero_row$f': ( 'B$' * 'A_b_vec_c_vec_b_vec_b_vec$' ) > $o ).

tff('uuv$',type,
    'uuv$': 'Num_set$' > 'Num_bool_fun$' ).

tff('fun_app$k',type,
    'fun_app$k': ( 'C_c_fun$' * 'C$' ) > 'C$' ).

tff('collect$b',type,
    'collect$b': 'Int_bool_fun$' > 'Int_set$' ).

tff('one$e',type,
    'one$e': 'A_b_vec_c_vec$' ).

tff('fun_app$',type,
    'fun_app$': ( 'Nat_nat_fun$' * 'Nat$' ) > 'Nat$' ).

tff('fun_app$d',type,
    'fun_app$d': ( 'Num_bool_fun$' * 'Num$' ) > $o ).

tff('is_zero_row$h',type,
    'is_zero_row$h': ( 'B$' * 'Nat_b_vec_b_vec$' ) > $o ).

tff('plus$a',type,
    'plus$a': 'C$' > 'C_c_fun$' ).

tff('vec_nth$c',type,
    'vec_nth$c': ( 'A_b_vec_c_vec_b_vec_c_vec$' * 'C$' ) > 'A_b_vec_c_vec_b_vec$' ).

tff('of_nat_aux$',type,
    'of_nat_aux$': ( 'Nat_nat_fun$' * 'Nat$' ) > 'Nat_nat_fun$' ).

tff('fun_app$p',type,
    'fun_app$p': ( 'A_a_fun$' * 'A$' ) > 'A$' ).

tff('reduced_row_echelon_form_upt_k$',type,
    'reduced_row_echelon_form_upt_k$': 'A_b_vec_c_vec$' > 'Nat_bool_fun$' ).

tff('uuf$',type,
    'uuf$': ( 'A_b_vec_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('fun_app$w',type,
    'fun_app$w': ( 'Int_b_fun$' * $int ) > 'B$' ).

tff('vec_nth$d',type,
    'vec_nth$d': ( 'A_b_vec_c_vec_b_vec_b_vec$' * 'B$' ) > 'A_b_vec_c_vec_b_vec$' ).

tff('one$d',type,
    'one$d': 'A_b_vec$' ).

tff('vec_nth$a',type,
    'vec_nth$a': 'A_b_vec_c_vec$' > 'C_a_b_vec_fun$' ).

tff('reduced_row_echelon_form$c',type,
    'reduced_row_echelon_form$c': 'A_b_vec_b_vec_c_vec$' > $o ).

tff('less_eq$',type,
    'less_eq$': 'Nat_nat_bool_fun_fun$' ).

tff('num_of_nat$',type,
    'num_of_nat$': 'Nat$' > 'Num$' ).

tff('zero$b',type,
    'zero$b': 'A_b_vec$' ).

tff('less$b',type,
    'less$b': 'Nat_nat_bool_fun_fun$' ).

tff('zero$',type,
    'zero$': 'A$' ).

tff('reduced_row_echelon_form$i',type,
    'reduced_row_echelon_form$i': 'A_b_vec_b_vec$' > $o ).

tff('collect$a',type,
    'collect$a': 'Num_bool_fun$' > 'Num_set$' ).

tff(tlfalse,type,
    tlfalse: tlbool ).

tff('is_zero_row$c',type,
    'is_zero_row$c': ( 'C$' * 'A_b_vec_b_vec_c_vec$' ) > $o ).

tff('vec$a',type,
    'vec$a': 'A$' > 'A_b_vec$' ).

tff('is_zero_row$e',type,
    'is_zero_row$e': ( 'B$' * 'Int_b_vec_b_vec$' ) > $o ).

tff('member$',type,
    'member$': ( 'Num$' * 'Num_set$' ) > $o ).

tff('fun_app$c',type,
    'fun_app$c': ( 'Int_int_bool_fun_fun$' * $int ) > 'Int_bool_fun$' ).

tff('vec_nth$',type,
    'vec_nth$': 'A_b_vec$' > 'B_a_fun$' ).

tff('row$',type,
    'row$': ( 'C$' * 'A_b_vec_c_vec$' ) > 'A_b_vec$' ).

tff('vec$',type,
    'vec$': 'A_b_vec$' > 'A_b_vec_c_vec$' ).

tff('reduced_row_echelon_form$b',type,
    'reduced_row_echelon_form$b': 'A_b_vec_c_vec_b_vec_c_vec$' > $o ).

tff('zero$d',type,
    'zero$d': 'Nat_set$' ).

tff('member$b',type,
    'member$b': ( $int * 'Int_set$' ) > $o ).

tff('uuw$',type,
    'uuw$': 'Int_set$' > 'Int_bool_fun$' ).

tff('vec_nth$h',type,
    'vec_nth$h': 'Nat_b_vec$' > 'B_nat_fun$' ).

tff('vec_nth$i',type,
    'vec_nth$i': ( 'Nat_b_vec_c_vec$' * 'C$' ) > 'Nat_b_vec$' ).

tff('fun_app$r',type,
    'fun_app$r': ( 'B_a_bool_fun_fun$' * 'B$' ) > 'A_bool_fun$' ).

tff('one$a',type,
    'one$a': 'C$' ).

tff('vec_nth$e',type,
    'vec_nth$e': ( 'A_b_vec_b_vec$' * 'B$' ) > 'A_b_vec$' ).

tff('fun_app$m',type,
    'fun_app$m': ( 'B_b_fun$' * 'B$' ) > 'B$' ).

tff('suc$',type,
    'suc$': 'Nat_nat_fun$' ).

tff('uuu$',type,
    'uuu$': 'Nat_set$' > 'Nat_bool_fun$' ).

tff('uuq$',type,
    'uuq$': 'Nat_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('uuy$',type,
    'uuy$': 'Nat_bool_fun$' > 'Nat_bool_fun$' ).

tff('uus$',type,
    'uus$': 'A_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('vec_nth$g',type,
    'vec_nth$g': ( 'A_b_vec_b_vec_b_vec$' * 'B$' ) > 'A_b_vec_b_vec$' ).

tff('fun_app$n',type,
    'fun_app$n': ( 'B_nat_fun$' * 'B$' ) > 'Nat$' ).

tff('dbl_dec$',type,
    'dbl_dec$': 'Int_int_fun$' ).

tff('reduced_row_echelon_form$e',type,
    'reduced_row_echelon_form$e': 'Int_b_vec_b_vec$' > $o ).

tff('a$',type,
    'a$': 'A_b_vec_c_vec$' ).

tff('is_zero_row$',type,
    'is_zero_row$': ( 'C$' * 'A_b_vec_c_vec$' ) > $o ).

tff('uuk$',type,
    'uuk$': 'Int_b_vec_b_vec$' > 'B_b_bool_fun_fun$' ).

tff('zero$c',type,
    'zero$c': 'Nat$' ).

tff('fun_app$b',type,
    'fun_app$b': ( 'Int_bool_fun$' * $int ) > $o ).

tff('plus$c',type,
    'plus$c': ( 'Nat_set$' * 'Nat_set$' ) > 'Nat_set$' ).

tff('reduced_row_echelon_form$d',type,
    'reduced_row_echelon_form$d': 'Nat_b_vec_c_vec$' > $o ).

tff('plus$e',type,
    'plus$e': ( 'Num$' * 'Num$' ) > 'Num$' ).

tff('uue$',type,
    'uue$': ( 'A_b_vec_c_vec_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('uud$',type,
    'uud$': ( 'A_b_vec_c_vec_b_vec_c_vec$' * 'C$' ) > 'B_bool_fun$' ).

tff('vec_nth$k',type,
    'vec_nth$k': 'Int_b_vec$' > 'B_int_fun$' ).

%% Assertions:
%% ∀ ?v0:Nat$ (fun_app$(uuz$, ?v0) = fun_app$(plus$(?v0), one$))
tff(axiom0,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('uuz$',A__questionmark_v0) = 'fun_app$'('plus$'(A__questionmark_v0),'one$') ) ).

%% ∀ ?v0:Int (fun_app$a(uva$, ?v0) = (?v0 + 1))
tff(axiom1,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$a'('uva$',A__questionmark_v0) = $sum(A__questionmark_v0,1) ) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$b(fun_app$c(uux$, ?v0), ?v1) = (?v0 < ?v1))
tff(axiom2,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( 'fun_app$b'('fun_app$c'('uux$',A__questionmark_v0),A__questionmark_v1)
    <=> $less(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Num_set$ ?v1:Num$ (fun_app$d(uuv$(?v0), ?v1) = member$(?v1, ?v0))
tff(axiom3,axiom,
    ! [A__questionmark_v0: 'Num_set$',A__questionmark_v1: 'Num$'] :
      ( 'fun_app$d'('uuv$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'member$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat$ (fun_app$e(uuu$(?v0), ?v1) = member$a(?v1, ?v0))
tff(axiom4,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('uuu$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'member$a'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int (fun_app$b(uuw$(?v0), ?v1) = member$b(?v1, ?v0))
tff(axiom5,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: $int] :
      ( 'fun_app$b'('uuw$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'member$b'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (fun_app$e(uuy$(?v0), ?v1) = fun_app$e(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1))))
tff(axiom6,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('uuy$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))) ) ).

%% ∀ ?v0:C$ ?v1:B$ (fun_app$h(uu$(?v0), ?v1) = ¬(fun_app$i(vec_nth$(fun_app$j(vec_nth$a(a$), ?v0)), ?v1) = zero$))
tff(axiom7,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('uu$'(A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'('a$'),A__questionmark_v0)),A__questionmark_v1) != 'zero$' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uue$(?v0, ?v1), ?v2) = ¬(vec_nth$b(vec_nth$c(?v0, fun_app$k(plus$a(?v1), one$a)), ?v2) = zero$a))
tff(axiom8,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uue$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$b'('vec_nth$c'(A__questionmark_v0,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a')),A__questionmark_v2) != 'zero$a' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uum$(?v0), ?v1), ?v2) = ¬(vec_nth$b(vec_nth$d(?v0, fun_app$m(plus$b(?v1), one$b)), ?v2) = zero$a))
tff(axiom9,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uum$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$b'('vec_nth$d'(A__questionmark_v0,'fun_app$m'('plus$b'(A__questionmark_v1),'one$b')),A__questionmark_v2) != 'zero$a' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uug$(?v0, ?v1), ?v2) = ¬(vec_nth$e(vec_nth$f(?v0, fun_app$k(plus$a(?v1), one$a)), ?v2) = zero$b))
tff(axiom10,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uug$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$e'('vec_nth$f'(A__questionmark_v0,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a')),A__questionmark_v2) != 'zero$b' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uuo$(?v0), ?v1), ?v2) = ¬(vec_nth$e(vec_nth$g(?v0, fun_app$m(plus$b(?v1), one$b)), ?v2) = zero$b))
tff(axiom11,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uuo$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$e'('vec_nth$g'(A__questionmark_v0,'fun_app$m'('plus$b'(A__questionmark_v1),'one$b')),A__questionmark_v2) != 'zero$b' ) ) ).

%% ∀ ?v0:Nat_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uui$(?v0, ?v1), ?v2) = ¬(fun_app$n(vec_nth$h(vec_nth$i(?v0, fun_app$k(plus$a(?v1), one$a))), ?v2) = zero$c))
tff(axiom12,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uui$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$n'('vec_nth$h'('vec_nth$i'(A__questionmark_v0,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))),A__questionmark_v2) != 'zero$c' ) ) ).

%% ∀ ?v0:Nat_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uuq$(?v0), ?v1), ?v2) = ¬(fun_app$n(vec_nth$h(vec_nth$j(?v0, fun_app$m(plus$b(?v1), one$b))), ?v2) = zero$c))
tff(axiom13,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uuq$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$n'('vec_nth$h'('vec_nth$j'(A__questionmark_v0,'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))),A__questionmark_v2) != 'zero$c' ) ) ).

%% ∀ ?v0:Int_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uuc$(?v0, ?v1), ?v2) = ¬(fun_app$o(vec_nth$k(vec_nth$l(?v0, fun_app$k(plus$a(?v1), one$a))), ?v2) = 0))
tff(axiom14,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uuc$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$o'('vec_nth$k'('vec_nth$l'(A__questionmark_v0,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))),A__questionmark_v2) != 0 ) ) ).

%% ∀ ?v0:Int_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uuk$(?v0), ?v1), ?v2) = ¬(fun_app$o(vec_nth$k(vec_nth$m(?v0, fun_app$m(plus$b(?v1), one$b))), ?v2) = 0))
tff(axiom15,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uuk$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$o'('vec_nth$k'('vec_nth$m'(A__questionmark_v0,'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))),A__questionmark_v2) != 0 ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uut$(?v0, ?v1), ?v2) = ¬(fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), fun_app$k(plus$a(?v1), one$a))), ?v2) = zero$))
tff(axiom16,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uut$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))),A__questionmark_v2) != 'zero$' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uus$(?v0), ?v1), ?v2) = ¬(fun_app$i(vec_nth$(vec_nth$e(?v0, fun_app$m(plus$b(?v1), one$b))), ?v2) = zero$))
tff(axiom17,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uus$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$i'('vec_nth$'('vec_nth$e'(A__questionmark_v0,'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))),A__questionmark_v2) != 'zero$' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uud$(?v0, ?v1), ?v2) = ¬(vec_nth$b(vec_nth$c(?v0, ?v1), ?v2) = zero$a))
tff(axiom18,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uud$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$b'('vec_nth$c'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) != 'zero$a' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uul$(?v0), ?v1), ?v2) = ¬(vec_nth$b(vec_nth$d(?v0, ?v1), ?v2) = zero$a))
tff(axiom19,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uul$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$b'('vec_nth$d'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) != 'zero$a' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uuf$(?v0, ?v1), ?v2) = ¬(vec_nth$e(vec_nth$f(?v0, ?v1), ?v2) = zero$b))
tff(axiom20,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uuf$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$e'('vec_nth$f'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) != 'zero$b' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uun$(?v0), ?v1), ?v2) = ¬(vec_nth$e(vec_nth$g(?v0, ?v1), ?v2) = zero$b))
tff(axiom21,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uun$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'vec_nth$e'('vec_nth$g'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) != 'zero$b' ) ) ).

%% ∀ ?v0:Nat_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uuh$(?v0, ?v1), ?v2) = ¬(fun_app$n(vec_nth$h(vec_nth$i(?v0, ?v1)), ?v2) = zero$c))
tff(axiom22,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uuh$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$n'('vec_nth$h'('vec_nth$i'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) != 'zero$c' ) ) ).

%% ∀ ?v0:Nat_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uup$(?v0), ?v1), ?v2) = ¬(fun_app$n(vec_nth$h(vec_nth$j(?v0, ?v1)), ?v2) = zero$c))
tff(axiom23,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uup$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$n'('vec_nth$h'('vec_nth$j'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) != 'zero$c' ) ) ).

%% ∀ ?v0:Int_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uub$(?v0, ?v1), ?v2) = ¬(fun_app$o(vec_nth$k(vec_nth$l(?v0, ?v1)), ?v2) = 0))
tff(axiom24,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uub$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$o'('vec_nth$k'('vec_nth$l'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) != 0 ) ) ).

%% ∀ ?v0:Int_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uuj$(?v0), ?v1), ?v2) = ¬(fun_app$o(vec_nth$k(vec_nth$m(?v0, ?v1)), ?v2) = 0))
tff(axiom25,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uuj$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$o'('vec_nth$k'('vec_nth$m'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) != 0 ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:C$ ?v2:B$ (fun_app$h(uua$(?v0, ?v1), ?v2) = ¬(fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v1)), ?v2) = zero$))
tff(axiom26,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'C$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('uua$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) != 'zero$' ) ) ).

%% ∀ ?v0:A_b_vec_b_vec$ ?v1:B$ ?v2:B$ (fun_app$h(fun_app$l(uur$(?v0), ?v1), ?v2) = ¬(fun_app$i(vec_nth$(vec_nth$e(?v0, ?v1)), ?v2) = zero$))
tff(axiom27,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('uur$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$i'('vec_nth$'('vec_nth$e'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) != 'zero$' ) ) ).

%% ¬∀ ?v0:C$ (¬is_zero_row$(?v0, a$) ⇒ ∀ ?v1:C$ (¬(?v0 = ?v1) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(a$), ?v1)), least$(uu$(?v0))) = zero$)))
tff(conjecture28,conjecture,
    ! [A__questionmark_v0: 'C$'] :
      ( ~ 'is_zero_row$'(A__questionmark_v0,'a$')
     => ! [A__questionmark_v1: 'C$'] :
          ( ( A__questionmark_v0 != A__questionmark_v1 )
         => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'('a$'),A__questionmark_v1)),'least$'('uu$'(A__questionmark_v0))) = 'zero$' ) ) ) ).

%% reduced_row_echelon_form$(a$)
tff(axiom29,axiom,
    'reduced_row_echelon_form$'('a$') ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ (is_zero_row$(?v0, ?v1) = ∀ ?v2:B$ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v1), ?v0)), ?v2) = zero$))
tff(axiom30,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'B$'] : ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v0)),A__questionmark_v2) = 'zero$' ) ) ).

%% ∀ ?v0:B$ (fun_app$i(vec_nth$(zero$b), ?v0) = zero$)
tff(axiom31,axiom,
    ! [A__questionmark_v0: 'B$'] : ( 'fun_app$i'('vec_nth$'('zero$b'),A__questionmark_v0) = 'zero$' ) ).

%% ∀ ?v0:C$ (fun_app$j(vec_nth$a(zero$a), ?v0) = zero$b)
tff(axiom32,axiom,
    ! [A__questionmark_v0: 'C$'] : ( 'fun_app$j'('vec_nth$a'('zero$a'),A__questionmark_v0) = 'zero$b' ) ).

%% ∀ ?v0:A_b_vec_c_vec$ (reduced_row_echelon_form$(?v0) ⇒ ∀ ?v1:C$ (¬is_zero_row$(?v1, ?v0) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v1)), least$(uua$(?v0, ?v1))) = one$c)))
tff(axiom33,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ~ 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
         => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v1)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v1))) = 'one$c' ) ) ) ).

%% ∀ ?v0:B_bool_fun$ ?v1:B$ (fun_app$h(?v0, ?v1) ⇒ fun_app$h(?v0, least$(?v0)))
tff(axiom34,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'(A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$h'(A__questionmark_v0,'least$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (fun_app$e(?v0, ?v1) ⇒ fun_app$e(?v0, least$a(?v0)))
tff(axiom35,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$e'(A__questionmark_v0,'least$a'(A__questionmark_v0)) ) ).

%% ∀ ?v0:A_a_fun$ ?v1:A_b_vec_c_vec$ ?v2:C$ ?v3:B$ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(map_matrix$(?v0, ?v1)), ?v2)), ?v3) = fun_app$p(?v0, fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v1), ?v2)), ?v3)))
tff(axiom36,axiom,
    ! [A__questionmark_v0: 'A_a_fun$',A__questionmark_v1: 'A_b_vec_c_vec$',A__questionmark_v2: 'C$',A__questionmark_v3: 'B$'] : ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'('map_matrix$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2)),A__questionmark_v3) = 'fun_app$p'(A__questionmark_v0,'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2)),A__questionmark_v3)) ) ).

%% ∀ ?v0:B_bool_fun$ ?v1:B$ ?v2:B_bool_fun$ ((fun_app$h(?v0, ?v1) ∧ ∀ ?v3:B$ (fun_app$h(?v0, ?v3) ⇒ fun_app$h(?v2, ?v3))) ⇒ fun_app$h(?v2, least$(?v0)))
tff(axiom37,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_bool_fun$'] :
      ( ( 'fun_app$h'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v3: 'B$'] :
            ( 'fun_app$h'(A__questionmark_v0,A__questionmark_v3)
           => 'fun_app$h'(A__questionmark_v2,A__questionmark_v3) ) )
     => 'fun_app$h'(A__questionmark_v2,'least$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ?v2:Nat_bool_fun$ ((fun_app$e(?v0, ?v1) ∧ ∀ ?v3:Nat$ (fun_app$e(?v0, ?v3) ⇒ fun_app$e(?v2, ?v3))) ⇒ fun_app$e(?v2, least$a(?v0)))
tff(axiom38,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v3)
           => 'fun_app$e'(A__questionmark_v2,A__questionmark_v3) ) )
     => 'fun_app$e'(A__questionmark_v2,'least$a'(A__questionmark_v0)) ) ).

%% ∀ ?v0:B_bool_fun$ (∃ ?v1:B$ fun_app$h(?v0, ?v1) ⇒ fun_app$h(?v0, least$(?v0)))
tff(axiom39,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$'] :
      ( ? [A__questionmark_v1: 'B$'] : 'fun_app$h'(A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$h'(A__questionmark_v0,'least$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∃ ?v1:Nat$ fun_app$e(?v0, ?v1) ⇒ fun_app$e(?v0, least$a(?v0)))
tff(axiom40,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v1: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$e'(A__questionmark_v0,'least$a'(A__questionmark_v0)) ) ).

%% ∀ ?v0:B_bool_fun$ ?v1:B_bool_fun$ ((∃ ?v2:B$ fun_app$h(?v0, ?v2) ∧ ∀ ?v2:B$ (fun_app$h(?v0, ?v2) ⇒ fun_app$h(?v1, ?v2))) ⇒ fun_app$h(?v1, least$(?v0)))
tff(axiom41,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$',A__questionmark_v1: 'B_bool_fun$'] :
      ( ( ? [A__questionmark_v2: 'B$'] : 'fun_app$h'(A__questionmark_v0,A__questionmark_v2)
        & ! [A__questionmark_v2: 'B$'] :
            ( 'fun_app$h'(A__questionmark_v0,A__questionmark_v2)
           => 'fun_app$h'(A__questionmark_v1,A__questionmark_v2) ) )
     => 'fun_app$h'(A__questionmark_v1,'least$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat_bool_fun$ ((∃ ?v2:Nat$ fun_app$e(?v0, ?v2) ∧ ∀ ?v2:Nat$ (fun_app$e(?v0, ?v2) ⇒ fun_app$e(?v1, ?v2))) ⇒ fun_app$e(?v1, least$a(?v0)))
tff(axiom42,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ( ? [A__questionmark_v2: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v2)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v2)
           => 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) ) )
     => 'fun_app$e'(A__questionmark_v1,'least$a'(A__questionmark_v0)) ) ).

%% ∀ ?v0:A_b_vec$ ?v1:A_b_vec$ ((vec_nth$(?v0) = vec_nth$(?v1)) = (?v0 = ?v1))
tff(axiom43,axiom,
    ! [A__questionmark_v0: 'A_b_vec$',A__questionmark_v1: 'A_b_vec$'] :
      ( ( 'vec_nth$'(A__questionmark_v0) = 'vec_nth$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:A_b_vec_c_vec$ ((vec_nth$a(?v0) = vec_nth$a(?v1)) = (?v0 = ?v1))
tff(axiom44,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( ( 'vec_nth$a'(A__questionmark_v0) = 'vec_nth$a'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:B_a_bool_fun_fun$ (∀ ?v1:B$ ∃ ?v2:A$ fun_app$q(fun_app$r(?v0, ?v1), ?v2) = ∃ ?v1:A_b_vec$ ∀ ?v2:B$ fun_app$q(fun_app$r(?v0, ?v2), fun_app$i(vec_nth$(?v1), ?v2)))
tff(axiom45,axiom,
    ! [A__questionmark_v0: 'B_a_bool_fun_fun$'] :
      ( ! [A__questionmark_v1: 'B$'] :
        ? [A__questionmark_v2: 'A$'] : 'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ? [A__questionmark_v1: 'A_b_vec$'] :
        ! [A__questionmark_v2: 'B$'] : 'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v2),'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:C_a_b_vec_bool_fun_fun$ (∀ ?v1:C$ ∃ ?v2:A_b_vec$ fun_app$s(fun_app$t(?v0, ?v1), ?v2) = ∃ ?v1:A_b_vec_c_vec$ ∀ ?v2:C$ fun_app$s(fun_app$t(?v0, ?v2), fun_app$j(vec_nth$a(?v1), ?v2)))
tff(axiom46,axiom,
    ! [A__questionmark_v0: 'C_a_b_vec_bool_fun_fun$'] :
      ( ! [A__questionmark_v1: 'C$'] :
        ? [A__questionmark_v2: 'A_b_vec$'] : 'fun_app$s'('fun_app$t'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ? [A__questionmark_v1: 'A_b_vec_c_vec$'] :
        ! [A__questionmark_v2: 'C$'] : 'fun_app$s'('fun_app$t'(A__questionmark_v0,A__questionmark_v2),'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:B$ (fun_app$i(vec_nth$(one$d), ?v0) = one$c)
tff(axiom47,axiom,
    ! [A__questionmark_v0: 'B$'] : ( 'fun_app$i'('vec_nth$'('one$d'),A__questionmark_v0) = 'one$c' ) ).

%% ∀ ?v0:C$ (fun_app$j(vec_nth$a(one$e), ?v0) = one$d)
tff(axiom48,axiom,
    ! [A__questionmark_v0: 'C$'] : ( 'fun_app$j'('vec_nth$a'('one$e'),A__questionmark_v0) = 'one$d' ) ).

%% ∀ ?v0:A$ ((one$c = ?v0) = (?v0 = one$c))
tff(axiom49,axiom,
    ! [A__questionmark_v0: 'A$'] :
      ( ( 'one$c' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'one$c' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ((one$e = ?v0) = (?v0 = one$e))
tff(axiom50,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( ( 'one$e' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'one$e' ) ) ).

%% ∀ ?v0:A_b_vec$ ((one$d = ?v0) = (?v0 = one$d))
tff(axiom51,axiom,
    ! [A__questionmark_v0: 'A_b_vec$'] :
      ( ( 'one$d' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'one$d' ) ) ).

%% ∀ ?v0:C$ ((one$a = ?v0) = (?v0 = one$a))
tff(axiom52,axiom,
    ! [A__questionmark_v0: 'C$'] :
      ( ( 'one$a' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'one$a' ) ) ).

%% ∀ ?v0:Nat$ ((one$ = ?v0) = (?v0 = one$))
tff(axiom53,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'one$' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'one$' ) ) ).

%% ∀ ?v0:Int ((1 = ?v0) = (?v0 = 1))
tff(axiom54,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 1 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 1 ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ((zero$a = ?v0) = (?v0 = zero$a))
tff(axiom55,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( ( 'zero$a' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$a' ) ) ).

%% ∀ ?v0:A_b_vec$ ((zero$b = ?v0) = (?v0 = zero$b))
tff(axiom56,axiom,
    ! [A__questionmark_v0: 'A_b_vec$'] :
      ( ( 'zero$b' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$b' ) ) ).

%% ∀ ?v0:Nat$ ((zero$c = ?v0) = (?v0 = zero$c))
tff(axiom57,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'zero$c' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$c' ) ) ).

%% ∀ ?v0:A$ ((zero$ = ?v0) = (?v0 = zero$))
tff(axiom58,axiom,
    ! [A__questionmark_v0: 'A$'] :
      ( ( 'zero$' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$' ) ) ).

%% ∀ ?v0:Int ((0 = ?v0) = (?v0 = 0))
tff(axiom59,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Bool ?v1:A_b_vec$ ?v2:A_b_vec$ ?v3:B$ (fun_app$i(vec_nth$((if ?v0 ?v1 else ?v2)), ?v3) = (if ?v0 fun_app$i(vec_nth$(?v1), ?v3) else fun_app$i(vec_nth$(?v2), ?v3)))
tff(axiom60,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'A_b_vec$',A__questionmark_v2: 'A_b_vec$',A__questionmark_v3: 'B$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$i'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$i'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$i'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$i'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) ) ) ) ) ) ).

%% ∀ ?v0:Bool ?v1:A_b_vec_c_vec$ ?v2:A_b_vec_c_vec$ ?v3:C$ (fun_app$j(vec_nth$a((if ?v0 ?v1 else ?v2)), ?v3) = (if ?v0 fun_app$j(vec_nth$a(?v1), ?v3) else fun_app$j(vec_nth$a(?v2), ?v3)))
tff(axiom61,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'A_b_vec_c_vec$',A__questionmark_v2: 'A_b_vec_c_vec$',A__questionmark_v3: 'C$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec$ ?v1:A_b_vec$ ((?v0 = ?v1) = ∀ ?v2:B$ (fun_app$i(vec_nth$(?v0), ?v2) = fun_app$i(vec_nth$(?v1), ?v2)))
tff(axiom62,axiom,
    ! [A__questionmark_v0: 'A_b_vec$',A__questionmark_v1: 'A_b_vec$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ! [A__questionmark_v2: 'B$'] : ( 'fun_app$i'('vec_nth$'(A__questionmark_v0),A__questionmark_v2) = 'fun_app$i'('vec_nth$'(A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:A_b_vec_c_vec$ ((?v0 = ?v1) = ∀ ?v2:C$ (fun_app$j(vec_nth$a(?v0), ?v2) = fun_app$j(vec_nth$a(?v1), ?v2)))
tff(axiom63,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ! [A__questionmark_v2: 'C$'] : ( 'fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2) = 'fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ¬(zero$c = one$)
tff(axiom64,axiom,
    'zero$c' != 'one$' ).

%% ¬(0 = 1)
tff(axiom65,axiom,
    0 != 1 ).

%% ∀ ?v0:C$ ?v1:A_b_vec$ ((axis$(?v0, ?v1) = zero$a) = (?v1 = zero$b))
tff(axiom66,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec$'] :
      ( ( 'axis$'(A__questionmark_v0,A__questionmark_v1) = 'zero$a' )
    <=> ( A__questionmark_v1 = 'zero$b' ) ) ).

%% ∀ ?v0:B$ ?v1:A$ ((axis$a(?v0, ?v1) = zero$b) = (?v1 = zero$))
tff(axiom67,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'A$'] :
      ( ( 'axis$a'(A__questionmark_v0,A__questionmark_v1) = 'zero$b' )
    <=> ( A__questionmark_v1 = 'zero$' ) ) ).

%% ∀ ?v0:Int_b_vec_c_vec$ (reduced_row_echelon_form$a(?v0) = (∀ ?v1:C$ (is_zero_row$a(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$a(?v2, ?v0))) ∧ (∀ ?v1:C$ (¬is_zero_row$a(?v1, ?v0) ⇒ (fun_app$o(vec_nth$k(vec_nth$l(?v0, ?v1)), least$(uub$(?v0, ?v1))) = 1)) ∧ (∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$a(?v1, ?v0) ∧ ¬is_zero_row$a(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uub$(?v0, ?v1))), least$(uuc$(?v0, ?v1)))) ∧ ∀ ?v1:C$ (¬is_zero_row$a(?v1, ?v0) ⇒ ∀ ?v2:C$ (¬(?v1 = ?v2) ⇒ (fun_app$o(vec_nth$k(vec_nth$l(?v0, ?v2)), least$(uub$(?v0, ?v1))) = 0)))))))
tff(axiom68,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$a'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'C$'] :
            ( 'is_zero_row$a'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'C$'] :
                  ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                  & ~ 'is_zero_row$a'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$a'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$o'('vec_nth$k'('vec_nth$l'(A__questionmark_v0,A__questionmark_v1)),'least$'('uub$'(A__questionmark_v0,A__questionmark_v1))) = 1 ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
              & ~ 'is_zero_row$a'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$a'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uub$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uuc$'(A__questionmark_v0,A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$a'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'C$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$o'('vec_nth$k'('vec_nth$l'(A__questionmark_v0,A__questionmark_v2)),'least$'('uub$'(A__questionmark_v0,A__questionmark_v1))) = 0 ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_c_vec$ (reduced_row_echelon_form$b(?v0) = (∀ ?v1:C$ (is_zero_row$b(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$b(?v2, ?v0))) ∧ (∀ ?v1:C$ (¬is_zero_row$b(?v1, ?v0) ⇒ (vec_nth$b(vec_nth$c(?v0, ?v1), least$(uud$(?v0, ?v1))) = one$e)) ∧ (∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$b(?v1, ?v0) ∧ ¬is_zero_row$b(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uud$(?v0, ?v1))), least$(uue$(?v0, ?v1)))) ∧ ∀ ?v1:C$ (¬is_zero_row$b(?v1, ?v0) ⇒ ∀ ?v2:C$ (¬(?v1 = ?v2) ⇒ (vec_nth$b(vec_nth$c(?v0, ?v2), least$(uud$(?v0, ?v1))) = zero$a)))))))
tff(axiom69,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$b'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'C$'] :
            ( 'is_zero_row$b'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'C$'] :
                  ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                  & ~ 'is_zero_row$b'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$b'(A__questionmark_v1,A__questionmark_v0)
           => ( 'vec_nth$b'('vec_nth$c'(A__questionmark_v0,A__questionmark_v1),'least$'('uud$'(A__questionmark_v0,A__questionmark_v1))) = 'one$e' ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
              & ~ 'is_zero_row$b'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$b'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uud$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uue$'(A__questionmark_v0,A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$b'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'C$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'vec_nth$b'('vec_nth$c'(A__questionmark_v0,A__questionmark_v2),'least$'('uud$'(A__questionmark_v0,A__questionmark_v1))) = 'zero$a' ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_c_vec$ (reduced_row_echelon_form$c(?v0) = (∀ ?v1:C$ (is_zero_row$c(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$c(?v2, ?v0))) ∧ (∀ ?v1:C$ (¬is_zero_row$c(?v1, ?v0) ⇒ (vec_nth$e(vec_nth$f(?v0, ?v1), least$(uuf$(?v0, ?v1))) = one$d)) ∧ (∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$c(?v1, ?v0) ∧ ¬is_zero_row$c(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uuf$(?v0, ?v1))), least$(uug$(?v0, ?v1)))) ∧ ∀ ?v1:C$ (¬is_zero_row$c(?v1, ?v0) ⇒ ∀ ?v2:C$ (¬(?v1 = ?v2) ⇒ (vec_nth$e(vec_nth$f(?v0, ?v2), least$(uuf$(?v0, ?v1))) = zero$b)))))))
tff(axiom70,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$c'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'C$'] :
            ( 'is_zero_row$c'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'C$'] :
                  ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                  & ~ 'is_zero_row$c'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$c'(A__questionmark_v1,A__questionmark_v0)
           => ( 'vec_nth$e'('vec_nth$f'(A__questionmark_v0,A__questionmark_v1),'least$'('uuf$'(A__questionmark_v0,A__questionmark_v1))) = 'one$d' ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
              & ~ 'is_zero_row$c'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$c'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uuf$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uug$'(A__questionmark_v0,A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$c'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'C$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'vec_nth$e'('vec_nth$f'(A__questionmark_v0,A__questionmark_v2),'least$'('uuf$'(A__questionmark_v0,A__questionmark_v1))) = 'zero$b' ) ) ) ) ) ).

%% ∀ ?v0:Nat_b_vec_c_vec$ (reduced_row_echelon_form$d(?v0) = (∀ ?v1:C$ (is_zero_row$d(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$d(?v2, ?v0))) ∧ (∀ ?v1:C$ (¬is_zero_row$d(?v1, ?v0) ⇒ (fun_app$n(vec_nth$h(vec_nth$i(?v0, ?v1)), least$(uuh$(?v0, ?v1))) = one$)) ∧ (∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$d(?v1, ?v0) ∧ ¬is_zero_row$d(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uuh$(?v0, ?v1))), least$(uui$(?v0, ?v1)))) ∧ ∀ ?v1:C$ (¬is_zero_row$d(?v1, ?v0) ⇒ ∀ ?v2:C$ (¬(?v1 = ?v2) ⇒ (fun_app$n(vec_nth$h(vec_nth$i(?v0, ?v2)), least$(uuh$(?v0, ?v1))) = zero$c)))))))
tff(axiom71,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$d'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'C$'] :
            ( 'is_zero_row$d'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'C$'] :
                  ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                  & ~ 'is_zero_row$d'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$d'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$n'('vec_nth$h'('vec_nth$i'(A__questionmark_v0,A__questionmark_v1)),'least$'('uuh$'(A__questionmark_v0,A__questionmark_v1))) = 'one$' ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
              & ~ 'is_zero_row$d'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$d'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uuh$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uui$'(A__questionmark_v0,A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$d'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'C$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$n'('vec_nth$h'('vec_nth$i'(A__questionmark_v0,A__questionmark_v2)),'least$'('uuh$'(A__questionmark_v0,A__questionmark_v1))) = 'zero$c' ) ) ) ) ) ).

%% ∀ ?v0:Int_b_vec_b_vec$ (reduced_row_echelon_form$e(?v0) = (∀ ?v1:B$ (is_zero_row$e(?v1, ?v0) ⇒ ¬∃ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v1), ?v2) ∧ ¬is_zero_row$e(?v2, ?v0))) ∧ (∀ ?v1:B$ (¬is_zero_row$e(?v1, ?v0) ⇒ (fun_app$o(vec_nth$k(vec_nth$m(?v0, ?v1)), least$(fun_app$l(uuj$(?v0), ?v1))) = 1)) ∧ (∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$e(?v1, ?v0) ∧ ¬is_zero_row$e(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uuj$(?v0), ?v1))), least$(fun_app$l(uuk$(?v0), ?v1)))) ∧ ∀ ?v1:B$ (¬is_zero_row$e(?v1, ?v0) ⇒ ∀ ?v2:B$ (¬(?v1 = ?v2) ⇒ (fun_app$o(vec_nth$k(vec_nth$m(?v0, ?v2)), least$(fun_app$l(uuj$(?v0), ?v1))) = 0)))))))
tff(axiom72,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$e'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'B$'] :
            ( 'is_zero_row$e'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'B$'] :
                  ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2)
                  & ~ 'is_zero_row$e'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$e'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$o'('vec_nth$k'('vec_nth$m'(A__questionmark_v0,A__questionmark_v1)),'least$'('fun_app$l'('uuj$'(A__questionmark_v0),A__questionmark_v1))) = 1 ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
              & ~ 'is_zero_row$e'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$e'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uuj$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuk$'(A__questionmark_v0),A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$e'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'B$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$o'('vec_nth$k'('vec_nth$m'(A__questionmark_v0,A__questionmark_v2)),'least$'('fun_app$l'('uuj$'(A__questionmark_v0),A__questionmark_v1))) = 0 ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_b_vec$ (reduced_row_echelon_form$f(?v0) = (∀ ?v1:B$ (is_zero_row$f(?v1, ?v0) ⇒ ¬∃ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v1), ?v2) ∧ ¬is_zero_row$f(?v2, ?v0))) ∧ (∀ ?v1:B$ (¬is_zero_row$f(?v1, ?v0) ⇒ (vec_nth$b(vec_nth$d(?v0, ?v1), least$(fun_app$l(uul$(?v0), ?v1))) = one$e)) ∧ (∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$f(?v1, ?v0) ∧ ¬is_zero_row$f(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uul$(?v0), ?v1))), least$(fun_app$l(uum$(?v0), ?v1)))) ∧ ∀ ?v1:B$ (¬is_zero_row$f(?v1, ?v0) ⇒ ∀ ?v2:B$ (¬(?v1 = ?v2) ⇒ (vec_nth$b(vec_nth$d(?v0, ?v2), least$(fun_app$l(uul$(?v0), ?v1))) = zero$a)))))))
tff(axiom73,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$f'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'B$'] :
            ( 'is_zero_row$f'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'B$'] :
                  ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2)
                  & ~ 'is_zero_row$f'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$f'(A__questionmark_v1,A__questionmark_v0)
           => ( 'vec_nth$b'('vec_nth$d'(A__questionmark_v0,A__questionmark_v1),'least$'('fun_app$l'('uul$'(A__questionmark_v0),A__questionmark_v1))) = 'one$e' ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
              & ~ 'is_zero_row$f'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$f'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uul$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uum$'(A__questionmark_v0),A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$f'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'B$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'vec_nth$b'('vec_nth$d'(A__questionmark_v0,A__questionmark_v2),'least$'('fun_app$l'('uul$'(A__questionmark_v0),A__questionmark_v1))) = 'zero$a' ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_b_vec$ (reduced_row_echelon_form$g(?v0) = (∀ ?v1:B$ (is_zero_row$g(?v1, ?v0) ⇒ ¬∃ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v1), ?v2) ∧ ¬is_zero_row$g(?v2, ?v0))) ∧ (∀ ?v1:B$ (¬is_zero_row$g(?v1, ?v0) ⇒ (vec_nth$e(vec_nth$g(?v0, ?v1), least$(fun_app$l(uun$(?v0), ?v1))) = one$d)) ∧ (∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$g(?v1, ?v0) ∧ ¬is_zero_row$g(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uun$(?v0), ?v1))), least$(fun_app$l(uuo$(?v0), ?v1)))) ∧ ∀ ?v1:B$ (¬is_zero_row$g(?v1, ?v0) ⇒ ∀ ?v2:B$ (¬(?v1 = ?v2) ⇒ (vec_nth$e(vec_nth$g(?v0, ?v2), least$(fun_app$l(uun$(?v0), ?v1))) = zero$b)))))))
tff(axiom74,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$g'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'B$'] :
            ( 'is_zero_row$g'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'B$'] :
                  ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2)
                  & ~ 'is_zero_row$g'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$g'(A__questionmark_v1,A__questionmark_v0)
           => ( 'vec_nth$e'('vec_nth$g'(A__questionmark_v0,A__questionmark_v1),'least$'('fun_app$l'('uun$'(A__questionmark_v0),A__questionmark_v1))) = 'one$d' ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
              & ~ 'is_zero_row$g'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$g'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uun$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuo$'(A__questionmark_v0),A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$g'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'B$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'vec_nth$e'('vec_nth$g'(A__questionmark_v0,A__questionmark_v2),'least$'('fun_app$l'('uun$'(A__questionmark_v0),A__questionmark_v1))) = 'zero$b' ) ) ) ) ) ).

%% ∀ ?v0:Nat_b_vec_b_vec$ (reduced_row_echelon_form$h(?v0) = (∀ ?v1:B$ (is_zero_row$h(?v1, ?v0) ⇒ ¬∃ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v1), ?v2) ∧ ¬is_zero_row$h(?v2, ?v0))) ∧ (∀ ?v1:B$ (¬is_zero_row$h(?v1, ?v0) ⇒ (fun_app$n(vec_nth$h(vec_nth$j(?v0, ?v1)), least$(fun_app$l(uup$(?v0), ?v1))) = one$)) ∧ (∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$h(?v1, ?v0) ∧ ¬is_zero_row$h(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uup$(?v0), ?v1))), least$(fun_app$l(uuq$(?v0), ?v1)))) ∧ ∀ ?v1:B$ (¬is_zero_row$h(?v1, ?v0) ⇒ ∀ ?v2:B$ (¬(?v1 = ?v2) ⇒ (fun_app$n(vec_nth$h(vec_nth$j(?v0, ?v2)), least$(fun_app$l(uup$(?v0), ?v1))) = zero$c)))))))
tff(axiom75,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$h'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'B$'] :
            ( 'is_zero_row$h'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'B$'] :
                  ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2)
                  & ~ 'is_zero_row$h'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$h'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$n'('vec_nth$h'('vec_nth$j'(A__questionmark_v0,A__questionmark_v1)),'least$'('fun_app$l'('uup$'(A__questionmark_v0),A__questionmark_v1))) = 'one$' ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
              & ~ 'is_zero_row$h'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$h'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uup$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuq$'(A__questionmark_v0),A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$h'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'B$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$n'('vec_nth$h'('vec_nth$j'(A__questionmark_v0,A__questionmark_v2)),'least$'('fun_app$l'('uup$'(A__questionmark_v0),A__questionmark_v1))) = 'zero$c' ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec$ (reduced_row_echelon_form$i(?v0) = (∀ ?v1:B$ (is_zero_row$i(?v1, ?v0) ⇒ ¬∃ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v1), ?v2) ∧ ¬is_zero_row$i(?v2, ?v0))) ∧ (∀ ?v1:B$ (¬is_zero_row$i(?v1, ?v0) ⇒ (fun_app$i(vec_nth$(vec_nth$e(?v0, ?v1)), least$(fun_app$l(uur$(?v0), ?v1))) = one$c)) ∧ (∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$i(?v1, ?v0) ∧ ¬is_zero_row$i(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uur$(?v0), ?v1))), least$(fun_app$l(uus$(?v0), ?v1)))) ∧ ∀ ?v1:B$ (¬is_zero_row$i(?v1, ?v0) ⇒ ∀ ?v2:B$ (¬(?v1 = ?v2) ⇒ (fun_app$i(vec_nth$(vec_nth$e(?v0, ?v2)), least$(fun_app$l(uur$(?v0), ?v1))) = zero$)))))))
tff(axiom76,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$i'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'B$'] :
            ( 'is_zero_row$i'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'B$'] :
                  ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2)
                  & ~ 'is_zero_row$i'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$i'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$i'('vec_nth$'('vec_nth$e'(A__questionmark_v0,A__questionmark_v1)),'least$'('fun_app$l'('uur$'(A__questionmark_v0),A__questionmark_v1))) = 'one$c' ) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
              & ~ 'is_zero_row$i'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$i'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uur$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uus$'(A__questionmark_v0),A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'B$'] :
            ( ~ 'is_zero_row$i'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'B$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$i'('vec_nth$'('vec_nth$e'(A__questionmark_v0,A__questionmark_v2)),'least$'('fun_app$l'('uur$'(A__questionmark_v0),A__questionmark_v1))) = 'zero$' ) ) ) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ (reduced_row_echelon_form$(?v0) = (∀ ?v1:C$ (is_zero_row$(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$(?v2, ?v0))) ∧ (∀ ?v1:C$ (¬is_zero_row$(?v1, ?v0) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v1)), least$(uua$(?v0, ?v1))) = one$c)) ∧ (∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$(?v1, ?v0) ∧ ¬is_zero_row$(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v0, ?v1))), least$(uut$(?v0, ?v1)))) ∧ ∀ ?v1:C$ (¬is_zero_row$(?v1, ?v0) ⇒ ∀ ?v2:C$ (¬(?v1 = ?v2) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v2)), least$(uua$(?v0, ?v1))) = zero$)))))))
tff(axiom77,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
    <=> ( ! [A__questionmark_v1: 'C$'] :
            ( 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v2: 'C$'] :
                  ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                  & ~ 'is_zero_row$'(A__questionmark_v2,A__questionmark_v0) ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v1)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v1))) = 'one$c' ) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
              & ~ 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row$'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uut$'(A__questionmark_v0,A__questionmark_v1))) )
        & ! [A__questionmark_v1: 'C$'] :
            ( ~ 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v2: 'C$'] :
                ( ( A__questionmark_v1 != A__questionmark_v2 )
               => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v1))) = 'zero$' ) ) ) ) ) ).

%% ∀ ?v0:Int_b_vec_c_vec$ (reduced_row_echelon_form$a(?v0) ⇒ ∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$a(?v1, ?v0) ∧ ¬is_zero_row$a(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uub$(?v0, ?v1))), least$(uuc$(?v0, ?v1)))))
tff(axiom78,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$a'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
            & ~ 'is_zero_row$a'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$a'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uub$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uuc$'(A__questionmark_v0,A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_c_vec$ (reduced_row_echelon_form$b(?v0) ⇒ ∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$b(?v1, ?v0) ∧ ¬is_zero_row$b(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uud$(?v0, ?v1))), least$(uue$(?v0, ?v1)))))
tff(axiom79,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$b'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
            & ~ 'is_zero_row$b'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$b'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uud$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uue$'(A__questionmark_v0,A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_c_vec$ (reduced_row_echelon_form$c(?v0) ⇒ ∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$c(?v1, ?v0) ∧ ¬is_zero_row$c(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uuf$(?v0, ?v1))), least$(uug$(?v0, ?v1)))))
tff(axiom80,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$c'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
            & ~ 'is_zero_row$c'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$c'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uuf$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uug$'(A__questionmark_v0,A__questionmark_v1))) ) ) ).

%% ∀ ?v0:Nat_b_vec_c_vec$ (reduced_row_echelon_form$d(?v0) ⇒ ∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$d(?v1, ?v0) ∧ ¬is_zero_row$d(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uuh$(?v0, ?v1))), least$(uui$(?v0, ?v1)))))
tff(axiom81,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$d'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
            & ~ 'is_zero_row$d'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$d'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uuh$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uui$'(A__questionmark_v0,A__questionmark_v1))) ) ) ).

%% ∀ ?v0:Int_b_vec_b_vec$ (reduced_row_echelon_form$e(?v0) ⇒ ∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$e(?v1, ?v0) ∧ ¬is_zero_row$e(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uuj$(?v0), ?v1))), least$(fun_app$l(uuk$(?v0), ?v1)))))
tff(axiom82,axiom,
    ! [A__questionmark_v0: 'Int_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$e'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'B$'] :
          ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
            & ~ 'is_zero_row$e'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$e'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uuj$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuk$'(A__questionmark_v0),A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec_b_vec_b_vec$ (reduced_row_echelon_form$f(?v0) ⇒ ∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$f(?v1, ?v0) ∧ ¬is_zero_row$f(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uul$(?v0), ?v1))), least$(fun_app$l(uum$(?v0), ?v1)))))
tff(axiom83,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$f'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'B$'] :
          ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
            & ~ 'is_zero_row$f'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$f'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uul$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uum$'(A__questionmark_v0),A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec_b_vec$ (reduced_row_echelon_form$g(?v0) ⇒ ∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$g(?v1, ?v0) ∧ ¬is_zero_row$g(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uun$(?v0), ?v1))), least$(fun_app$l(uuo$(?v0), ?v1)))))
tff(axiom84,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$g'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'B$'] :
          ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
            & ~ 'is_zero_row$g'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$g'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uun$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuo$'(A__questionmark_v0),A__questionmark_v1))) ) ) ).

%% ∀ ?v0:Nat_b_vec_b_vec$ (reduced_row_echelon_form$h(?v0) ⇒ ∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$h(?v1, ?v0) ∧ ¬is_zero_row$h(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uup$(?v0), ?v1))), least$(fun_app$l(uuq$(?v0), ?v1)))))
tff(axiom85,axiom,
    ! [A__questionmark_v0: 'Nat_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$h'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'B$'] :
          ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
            & ~ 'is_zero_row$h'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$h'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uup$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uuq$'(A__questionmark_v0),A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_b_vec$ (reduced_row_echelon_form$i(?v0) ⇒ ∀ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v1), fun_app$m(plus$b(?v1), one$b)) ∧ (¬is_zero_row$i(?v1, ?v0) ∧ ¬is_zero_row$i(fun_app$m(plus$b(?v1), one$b), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(fun_app$l(uur$(?v0), ?v1))), least$(fun_app$l(uus$(?v0), ?v1)))))
tff(axiom86,axiom,
    ! [A__questionmark_v0: 'A_b_vec_b_vec$'] :
      ( 'reduced_row_echelon_form$i'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'B$'] :
          ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),'fun_app$m'('plus$b'(A__questionmark_v1),'one$b'))
            & ~ 'is_zero_row$i'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$i'('fun_app$m'('plus$b'(A__questionmark_v1),'one$b'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('fun_app$l'('uur$'(A__questionmark_v0),A__questionmark_v1))),'least$'('fun_app$l'('uus$'(A__questionmark_v0),A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ (reduced_row_echelon_form$(?v0) ⇒ ∀ ?v1:C$ ((less$(?v1, fun_app$k(plus$a(?v1), one$a)) ∧ (¬is_zero_row$(?v1, ?v0) ∧ ¬is_zero_row$(fun_app$k(plus$a(?v1), one$a), ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v0, ?v1))), least$(uut$(?v0, ?v1)))))
tff(axiom87,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( ( 'less$'(A__questionmark_v1,'fun_app$k'('plus$a'(A__questionmark_v1),'one$a'))
            & ~ 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row$'('fun_app$k'('plus$a'(A__questionmark_v1),'one$a'),A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v0,A__questionmark_v1))),'least$'('uut$'(A__questionmark_v0,A__questionmark_v1))) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ ?v2:C$ ((fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ∧ ¬is_zero_row_upt_k$(?v2, ?v1, ?v0)) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v2)), least$(uua$(?v0, ?v2))) = one$c))
tff(axiom88,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'C$'] :
      ( ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
        & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0) )
     => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'one$c' ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ (fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ⇒ ∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v2)), least$(uua$(?v0, ?v2))) = one$c)))
tff(axiom89,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
     => ! [A__questionmark_v2: 'C$'] :
          ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
         => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'one$c' ) ) ) ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ (is_zero_row$(?v0, ?v1) = (row$(?v0, ?v1) = zero$b))
tff(axiom90,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'row$'(A__questionmark_v0,A__questionmark_v1) = 'zero$b' ) ) ).

%% (vec$(zero$b) = zero$a)
tff(axiom91,axiom,
    'vec$'('zero$b') = 'zero$a' ).

%% (vec$a(zero$) = zero$b)
tff(axiom92,axiom,
    'vec$a'('zero$') = 'zero$b' ).

%% ∀ ?v0:A_b_vec_c_vec$ (reduced_row_echelon_form$(?v0) ⇒ ∀ ?v1:C$ (is_zero_row$(?v1, ?v0) ⇒ ¬∃ ?v2:C$ (less$(?v1, ?v2) ∧ ¬is_zero_row$(?v2, ?v0))))
tff(axiom93,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'C$'] :
          ( 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
         => ~ ? [A__questionmark_v2: 'C$'] :
                ( 'less$'(A__questionmark_v1,A__questionmark_v2)
                & ~ 'is_zero_row$'(A__questionmark_v2,A__questionmark_v0) ) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v0 + ?v2)) = (?v1 = ?v2))
tff(axiom94,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v0,A__questionmark_v2) )
    <=> ( A__questionmark_v1 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$(plus$(?v0), ?v1) = fun_app$(plus$(?v0), ?v2)) = (?v1 = ?v2))
tff(axiom95,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2) )
    <=> ( A__questionmark_v1 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v2 + ?v1)) = (?v0 = ?v2))
tff(axiom96,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v2,A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$(plus$(?v0), ?v1) = fun_app$(plus$(?v2), ?v1)) = (?v0 = ?v2))
tff(axiom97,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:A_b_vec$ ?v1:A_b_vec$ ((vec$(?v0) = vec$(?v1)) = (?v0 = ?v1))
tff(axiom98,axiom,
    ! [A__questionmark_v0: 'A_b_vec$',A__questionmark_v1: 'A_b_vec$'] :
      ( ( 'vec$'(A__questionmark_v0) = 'vec$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A$ ?v1:A$ ((vec$a(?v0) = vec$a(?v1)) = (?v0 = ?v1))
tff(axiom99,axiom,
    ! [A__questionmark_v0: 'A$',A__questionmark_v1: 'A$'] :
      ( ( 'vec$a'(A__questionmark_v0) = 'vec$a'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_b_vec$ ?v1:A_b_vec$ ((vec$(?v0) = vec$(?v1)) = (?v0 = ?v1))
tff(axiom100,axiom,
    ! [A__questionmark_v0: 'A_b_vec$',A__questionmark_v1: 'A_b_vec$'] :
      ( ( 'vec$'(A__questionmark_v0) = 'vec$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A$ ?v1:A$ ((vec$a(?v0) = vec$a(?v1)) = (?v0 = ?v1))
tff(axiom101,axiom,
    ! [A__questionmark_v0: 'A$',A__questionmark_v1: 'A$'] :
      ( ( 'vec$a'(A__questionmark_v0) = 'vec$a'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ (¬fun_app$e(fun_app$u(less$b, zero$c), ?v0) = (?v0 = zero$c))
tff(axiom102,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ~ 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v0)
    <=> ( A__questionmark_v0 = 'zero$c' ) ) ).

%% ∀ ?v0:Nat_set$ (plus$c(?v0, zero$d) = ?v0)
tff(axiom103,axiom,
    ! [A__questionmark_v0: 'Nat_set$'] : ( 'plus$c'(A__questionmark_v0,'zero$d') = A__questionmark_v0 ) ).

%% ∀ ?v0:Int_set$ (plus$d(?v0, zero$e) = ?v0)
tff(axiom104,axiom,
    ! [A__questionmark_v0: 'Int_set$'] : ( 'plus$d'(A__questionmark_v0,'zero$e') = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ (fun_app$(plus$(?v0), zero$c) = ?v0)
tff(axiom105,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('plus$'(A__questionmark_v0),'zero$c') = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((?v0 + 0) = ?v0)
tff(axiom106,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(A__questionmark_v0,0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((0 = (?v0 + ?v0)) = (?v0 = 0))
tff(axiom107,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = $sum(A__questionmark_v0,A__questionmark_v0) )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$(plus$(?v0), ?v1) = ?v1) = (?v0 = zero$c))
tff(axiom108,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 )
    <=> ( A__questionmark_v0 = 'zero$c' ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) = ?v1) = (?v0 = 0))
tff(axiom109,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = A__questionmark_v1 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$(plus$(?v0), ?v1) = ?v0) = (?v1 = zero$c))
tff(axiom110,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 )
    <=> ( A__questionmark_v1 = 'zero$c' ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) = ?v0) = (?v1 = 0))
tff(axiom111,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = A__questionmark_v0 )
    <=> ( A__questionmark_v1 = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = fun_app$(plus$(?v1), ?v0)) = (?v1 = zero$c))
tff(axiom112,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v0) )
    <=> ( A__questionmark_v1 = 'zero$c' ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = (?v1 + ?v0)) = (?v1 = 0))
tff(axiom113,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v1,A__questionmark_v0) )
    <=> ( A__questionmark_v1 = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (member$a(?v0, collect$(?v1)) = fun_app$e(?v1, ?v0))
tff(axiom114,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( 'member$a'(A__questionmark_v0,'collect$'(A__questionmark_v1))
    <=> 'fun_app$e'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Num$ ?v1:Num_bool_fun$ (member$(?v0, collect$a(?v1)) = fun_app$d(?v1, ?v0))
tff(axiom115,axiom,
    ! [A__questionmark_v0: 'Num$',A__questionmark_v1: 'Num_bool_fun$'] :
      ( 'member$'(A__questionmark_v0,'collect$a'(A__questionmark_v1))
    <=> 'fun_app$d'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int_bool_fun$ (member$b(?v0, collect$b(?v1)) = fun_app$b(?v1, ?v0))
tff(axiom116,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_bool_fun$'] :
      ( 'member$b'(A__questionmark_v0,'collect$b'(A__questionmark_v1))
    <=> 'fun_app$b'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_set$ (collect$(uuu$(?v0)) = ?v0)
tff(axiom117,axiom,
    ! [A__questionmark_v0: 'Nat_set$'] : ( 'collect$'('uuu$'(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Num_set$ (collect$a(uuv$(?v0)) = ?v0)
tff(axiom118,axiom,
    ! [A__questionmark_v0: 'Num_set$'] : ( 'collect$a'('uuv$'(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int_set$ (collect$b(uuw$(?v0)) = ?v0)
tff(axiom119,axiom,
    ! [A__questionmark_v0: 'Int_set$'] : ( 'collect$b'('uuw$'(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = fun_app$(plus$(?v0), ?v1)) = (?v1 = zero$c))
tff(axiom120,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) )
    <=> ( A__questionmark_v1 = 'zero$c' ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = (?v0 + ?v1)) = (?v1 = 0))
tff(axiom121,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v0,A__questionmark_v1) )
    <=> ( A__questionmark_v1 = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$(plus$(?v0), ?v1) = zero$c) = ((?v0 = zero$c) ∧ (?v1 = zero$c)))
tff(axiom122,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'zero$c' )
    <=> ( ( A__questionmark_v0 = 'zero$c' )
        & ( A__questionmark_v1 = 'zero$c' ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((zero$c = fun_app$(plus$(?v0), ?v1)) = ((?v0 = zero$c) ∧ (?v1 = zero$c)))
tff(axiom123,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'zero$c' = 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) )
    <=> ( ( A__questionmark_v0 = 'zero$c' )
        & ( A__questionmark_v1 = 'zero$c' ) ) ) ).

%% ∀ ?v0:Nat_set$ (plus$c(zero$d, ?v0) = ?v0)
tff(axiom124,axiom,
    ! [A__questionmark_v0: 'Nat_set$'] : ( 'plus$c'('zero$d',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int_set$ (plus$d(zero$e, ?v0) = ?v0)
tff(axiom125,axiom,
    ! [A__questionmark_v0: 'Int_set$'] : ( 'plus$d'('zero$e',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ (fun_app$(plus$(zero$c), ?v0) = ?v0)
tff(axiom126,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('plus$'('zero$c'),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((0 + ?v0) = ?v0)
tff(axiom127,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(0,A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v0), ?v2)) = fun_app$e(fun_app$u(less$b, ?v1), ?v2))
tff(axiom128,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2))
    <=> 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) < (?v0 + ?v2)) = (?v1 < ?v2))
tff(axiom129,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v0,A__questionmark_v2))
    <=> $less(A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v2), ?v1)) = fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom130,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1))
    <=> 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) < (?v2 + ?v1)) = (?v0 < ?v2))
tff(axiom131,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v2,A__questionmark_v1))
    <=> $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A$ ?v1:B$ (fun_app$i(vec_nth$(vec$a(?v0)), ?v1) = ?v0)
tff(axiom132,axiom,
    ! [A__questionmark_v0: 'A$',A__questionmark_v1: 'B$'] : ( 'fun_app$i'('vec_nth$'('vec$a'(A__questionmark_v0)),A__questionmark_v1) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_b_vec$ ?v1:C$ (fun_app$j(vec_nth$a(vec$(?v0)), ?v1) = ?v0)
tff(axiom133,axiom,
    ! [A__questionmark_v0: 'A_b_vec$',A__questionmark_v1: 'C$'] : ( 'fun_app$j'('vec_nth$a'('vec$'(A__questionmark_v0)),A__questionmark_v1) = A__questionmark_v0 ) ).

%% ∀ ?v0:B$ ?v1:A$ (fun_app$i(vec_nth$(axis$a(?v0, ?v1)), ?v0) = ?v1)
tff(axiom134,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'A$'] : ( 'fun_app$i'('vec_nth$'('axis$a'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v1 ) ).

%% ∀ ?v0:C$ ?v1:A_b_vec$ (fun_app$j(vec_nth$a(axis$(?v0, ?v1)), ?v0) = ?v1)
tff(axiom135,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec$'] : ( 'fun_app$j'('vec_nth$a'('axis$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v1 ) ).

%% ∀ ?v0:Int ((0 < (?v0 + ?v0)) = (0 < ?v0))
tff(axiom136,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,$sum(A__questionmark_v0,A__questionmark_v0))
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int (((?v0 + ?v0) < 0) = (?v0 < 0))
tff(axiom137,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v0),0)
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), fun_app$(plus$(?v1), ?v0)) = fun_app$e(fun_app$u(less$b, zero$c), ?v1))
tff(axiom138,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v0))
    <=> 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < (?v1 + ?v0)) = (0 < ?v1))
tff(axiom139,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v0))
    <=> $less(0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), fun_app$(plus$(?v0), ?v1)) = fun_app$e(fun_app$u(less$b, zero$c), ?v1))
tff(axiom140,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1))
    <=> 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < (?v0 + ?v1)) = (0 < ?v1))
tff(axiom141,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,$sum(A__questionmark_v0,A__questionmark_v1))
    <=> $less(0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), ?v1) = fun_app$e(fun_app$u(less$b, ?v0), zero$c))
tff(axiom142,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1)
    <=> 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'zero$c') ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) < ?v1) = (?v0 < 0))
tff(axiom143,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v1)
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), ?v0) = fun_app$e(fun_app$u(less$b, ?v1), zero$c))
tff(axiom144,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0)
    <=> 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),'zero$c') ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) < ?v0) = (?v1 < 0))
tff(axiom145,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v0)
    <=> $less(A__questionmark_v1,0) ) ).

%% (vec$(one$d) = one$e)
tff(axiom146,axiom,
    'vec$'('one$d') = 'one$e' ).

%% (vec$a(one$c) = one$d)
tff(axiom147,axiom,
    'vec$a'('one$c') = 'one$d' ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ ?v2:Nat_set$ (plus$c(plus$c(?v0, ?v1), ?v2) = plus$c(?v0, plus$c(?v1, ?v2)))
tff(axiom148,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$'] : ( 'plus$c'('plus$c'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = 'plus$c'(A__questionmark_v0,'plus$c'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ ?v2:Int_set$ (plus$d(plus$d(?v0, ?v1), ?v2) = plus$d(?v0, plus$d(?v1, ?v2)))
tff(axiom149,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$'] : ( 'plus$d'('plus$d'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = 'plus$d'(A__questionmark_v0,'plus$d'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) + ?v2) = (?v0 + (?v1 + ?v2)))
tff(axiom150,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : ( $sum($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = $sum(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$(plus$(fun_app$(plus$(?v0), ?v1)), ?v2) = fun_app$(plus$(?v0), fun_app$(plus$(?v1), ?v2)))
tff(axiom151,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] : ( 'fun_app$'('plus$'('fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$'('plus$'(A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v2), ?v3)) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v2)), fun_app$(plus$(?v1), ?v3)))
tff(axiom152,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 < ?v1) ∧ (?v2 < ?v3)) ⇒ ((?v0 + ?v2) < (?v1 + ?v3)))
tff(axiom153,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v2,A__questionmark_v3) )
     => $less($sum(A__questionmark_v0,A__questionmark_v2),$sum(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ (((?v0 = ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v2), ?v3)) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v2)), fun_app$(plus$(?v1), ?v3)))
tff(axiom154,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 = ?v1) ∧ (?v2 < ?v3)) ⇒ ((?v0 + ?v2) < (?v1 + ?v3)))
tff(axiom155,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & $less(A__questionmark_v2,A__questionmark_v3) )
     => $less($sum(A__questionmark_v0,A__questionmark_v2),$sum(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ (?v2 = ?v3)) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v2)), fun_app$(plus$(?v1), ?v3)))
tff(axiom156,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v2 = A__questionmark_v3 ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 < ?v1) ∧ (?v2 = ?v3)) ⇒ ((?v0 + ?v2) < (?v1 + ?v3)))
tff(axiom157,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( A__questionmark_v2 = A__questionmark_v3 ) )
     => $less($sum(A__questionmark_v0,A__questionmark_v2),$sum(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 = ?v1) ∧ (?v2 = ?v3)) ⇒ ((?v0 + ?v2) = (?v1 + ?v3)))
tff(axiom158,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & ( A__questionmark_v2 = A__questionmark_v3 ) )
     => ( $sum(A__questionmark_v0,A__questionmark_v2) = $sum(A__questionmark_v1,A__questionmark_v3) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ (((?v0 = ?v1) ∧ (?v2 = ?v3)) ⇒ (fun_app$(plus$(?v0), ?v2) = fun_app$(plus$(?v1), ?v3)))
tff(axiom159,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & ( A__questionmark_v2 = A__questionmark_v3 ) )
     => ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2) = 'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v3) ) ) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ ?v2:Nat_set$ ?v3:Nat_set$ ((?v0 = plus$c(?v1, ?v2)) ⇒ (plus$c(?v0, ?v3) = plus$c(?v1, plus$c(?v2, ?v3))))
tff(axiom160,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$',A__questionmark_v3: 'Nat_set$'] :
      ( ( A__questionmark_v0 = 'plus$c'(A__questionmark_v1,A__questionmark_v2) )
     => ( 'plus$c'(A__questionmark_v0,A__questionmark_v3) = 'plus$c'(A__questionmark_v1,'plus$c'(A__questionmark_v2,A__questionmark_v3)) ) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ ?v2:Int_set$ ?v3:Int_set$ ((?v0 = plus$d(?v1, ?v2)) ⇒ (plus$d(?v0, ?v3) = plus$d(?v1, plus$d(?v2, ?v3))))
tff(axiom161,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$',A__questionmark_v3: 'Int_set$'] :
      ( ( A__questionmark_v0 = 'plus$d'(A__questionmark_v1,A__questionmark_v2) )
     => ( 'plus$d'(A__questionmark_v0,A__questionmark_v3) = 'plus$d'(A__questionmark_v1,'plus$d'(A__questionmark_v2,A__questionmark_v3)) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int ((?v0 = (?v1 + ?v2)) ⇒ ((?v0 + ?v3) = (?v1 + (?v2 + ?v3))))
tff(axiom162,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v1,A__questionmark_v2) )
     => ( $sum(A__questionmark_v0,A__questionmark_v3) = $sum(A__questionmark_v1,$sum(A__questionmark_v2,A__questionmark_v3)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((?v0 = fun_app$(plus$(?v1), ?v2)) ⇒ (fun_app$(plus$(?v0), ?v3) = fun_app$(plus$(?v1), fun_app$(plus$(?v2), ?v3))))
tff(axiom163,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2) )
     => ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v3) = 'fun_app$'('plus$'(A__questionmark_v1),'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v3)) ) ) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ ?v2:Nat_set$ ?v3:Nat_set$ ((?v0 = plus$c(?v1, ?v2)) ⇒ (plus$c(?v3, ?v0) = plus$c(?v1, plus$c(?v3, ?v2))))
tff(axiom164,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$',A__questionmark_v3: 'Nat_set$'] :
      ( ( A__questionmark_v0 = 'plus$c'(A__questionmark_v1,A__questionmark_v2) )
     => ( 'plus$c'(A__questionmark_v3,A__questionmark_v0) = 'plus$c'(A__questionmark_v1,'plus$c'(A__questionmark_v3,A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ ?v2:Int_set$ ?v3:Int_set$ ((?v0 = plus$d(?v1, ?v2)) ⇒ (plus$d(?v3, ?v0) = plus$d(?v1, plus$d(?v3, ?v2))))
tff(axiom165,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$',A__questionmark_v3: 'Int_set$'] :
      ( ( A__questionmark_v0 = 'plus$d'(A__questionmark_v1,A__questionmark_v2) )
     => ( 'plus$d'(A__questionmark_v3,A__questionmark_v0) = 'plus$d'(A__questionmark_v1,'plus$d'(A__questionmark_v3,A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int ((?v0 = (?v1 + ?v2)) ⇒ ((?v3 + ?v0) = (?v1 + (?v3 + ?v2))))
tff(axiom166,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v1,A__questionmark_v2) )
     => ( $sum(A__questionmark_v3,A__questionmark_v0) = $sum(A__questionmark_v1,$sum(A__questionmark_v3,A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((?v0 = fun_app$(plus$(?v1), ?v2)) ⇒ (fun_app$(plus$(?v3), ?v0) = fun_app$(plus$(?v1), fun_app$(plus$(?v3), ?v2))))
tff(axiom167,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2) )
     => ( 'fun_app$'('plus$'(A__questionmark_v3),A__questionmark_v0) = 'fun_app$'('plus$'(A__questionmark_v1),'fun_app$'('plus$'(A__questionmark_v3),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int ∃ ?v1:Int (?v1 < ?v0)
tff(axiom168,axiom,
    ! [A__questionmark_v0: $int] :
    ? [A__questionmark_v1: $int] : $less(A__questionmark_v1,A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ∃ ?v1:Nat$ fun_app$e(fun_app$u(less$b, ?v0), ?v1)
tff(axiom169,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
    ? [A__questionmark_v1: 'Nat$'] : 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1) ).

%% ∀ ?v0:Int ∃ ?v1:Int (?v0 < ?v1)
tff(axiom170,axiom,
    ! [A__questionmark_v0: $int] :
    ? [A__questionmark_v1: $int] : $less(A__questionmark_v0,A__questionmark_v1) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom171,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom172,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom173,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:B$ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v0)) ⇒ false)
tff(axiom174,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v0)) ⇒ false)
tff(axiom175,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 < ?v1) ∧ (?v1 < ?v0)) ⇒ false)
tff(axiom176,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ ?v2:Nat_set$ (plus$c(plus$c(?v0, ?v1), ?v2) = plus$c(?v0, plus$c(?v1, ?v2)))
tff(axiom177,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$'] : ( 'plus$c'('plus$c'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = 'plus$c'(A__questionmark_v0,'plus$c'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ ?v2:Int_set$ (plus$d(plus$d(?v0, ?v1), ?v2) = plus$d(?v0, plus$d(?v1, ?v2)))
tff(axiom178,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$'] : ( 'plus$d'('plus$d'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = 'plus$d'(A__questionmark_v0,'plus$d'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) + ?v2) = (?v0 + (?v1 + ?v2)))
tff(axiom179,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : ( $sum($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = $sum(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$(plus$(fun_app$(plus$(?v0), ?v1)), ?v2) = fun_app$(plus$(?v0), fun_app$(plus$(?v1), ?v2)))
tff(axiom180,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] : ( 'fun_app$'('plus$'('fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$'('plus$'(A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C$ (((?v0 = ?v1) ∧ less$(?v1, ?v2)) ⇒ less$(?v0, ?v2))
tff(axiom181,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'less$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B$ (((?v0 = ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v2)) ⇒ fun_app$h(fun_app$l(less$a, ?v0), ?v2))
tff(axiom182,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((?v0 = ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom183,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 = ?v1) ∧ (?v1 < ?v2)) ⇒ (?v0 < ?v2))
tff(axiom184,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C$ ((less$(?v0, ?v1) ∧ (?v1 = ?v2)) ⇒ less$(?v0, ?v2))
tff(axiom185,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C$'] :
      ( ( 'less$'(A__questionmark_v0,A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => 'less$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ (?v1 = ?v2)) ⇒ fun_app$h(fun_app$l(less$a, ?v0), ?v2))
tff(axiom186,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ (?v1 = ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom187,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 < ?v1) ∧ (?v1 = ?v2)) ⇒ (?v0 < ?v2))
tff(axiom188,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:B_bool_fun$ ?v1:B$ (∀ ?v2:B$ (∀ ?v3:B$ (fun_app$h(fun_app$l(less$a, ?v3), ?v2) ⇒ fun_app$h(?v0, ?v3)) ⇒ fun_app$h(?v0, ?v2)) ⇒ fun_app$h(?v0, ?v1))
tff(axiom189,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$',A__questionmark_v1: 'B$'] :
      ( ! [A__questionmark_v2: 'B$'] :
          ( ! [A__questionmark_v3: 'B$'] :
              ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v3),A__questionmark_v2)
             => 'fun_app$h'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$h'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$h'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (∀ ?v3:Nat$ (fun_app$e(fun_app$u(less$b, ?v3), ?v2) ⇒ fun_app$e(?v0, ?v3)) ⇒ fun_app$e(?v0, ?v2)) ⇒ fun_app$e(?v0, ?v1))
tff(axiom190,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ! [A__questionmark_v3: 'Nat$'] :
              ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v3),A__questionmark_v2)
             => 'fun_app$e'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v0 + ?v2)) = (?v1 = ?v2))
tff(axiom191,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v0,A__questionmark_v2) )
    <=> ( A__questionmark_v1 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (¬fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ (¬fun_app$h(fun_app$l(less$a, ?v1), ?v0) = (?v1 = ?v0)))
tff(axiom192,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ (¬fun_app$e(fun_app$u(less$b, ?v1), ?v0) = (?v1 = ?v0)))
tff(axiom193,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int (¬(?v0 < ?v1) ⇒ (¬(?v1 < ?v0) = (?v1 = ?v0)))
tff(axiom194,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ~ $less(A__questionmark_v0,A__questionmark_v1)
     => ( ~ $less(A__questionmark_v1,A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v2 + ?v1)) = (?v0 = ?v2))
tff(axiom195,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v2,A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ false) ∧ (((?v0 = ?v1) ⇒ false) ∧ (fun_app$h(fun_app$l(less$a, ?v1), ?v0) ⇒ false))) ⇒ false)
tff(axiom196,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( ( A__questionmark_v0 = A__questionmark_v1 )
         => $false )
        & ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ false) ∧ (((?v0 = ?v1) ⇒ false) ∧ (fun_app$e(fun_app$u(less$b, ?v1), ?v0) ⇒ false))) ⇒ false)
tff(axiom197,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( ( A__questionmark_v0 = A__questionmark_v1 )
         => $false )
        & ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ((((?v0 < ?v1) ⇒ false) ∧ (((?v0 = ?v1) ⇒ false) ∧ ((?v1 < ?v0) ⇒ false))) ⇒ false)
tff(axiom198,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( ( $less(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( ( A__questionmark_v0 = A__questionmark_v1 )
         => $false )
        & ( $less(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:B$ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v0)) ⇒ false)
tff(axiom199,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v0)) ⇒ false)
tff(axiom200,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 < ?v1) ∧ (?v1 < ?v0)) ⇒ false)
tff(axiom201,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ (plus$c(?v0, ?v1) = plus$c(?v1, ?v0))
tff(axiom202,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$'] : ( 'plus$c'(A__questionmark_v0,A__questionmark_v1) = 'plus$c'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ (plus$d(?v0, ?v1) = plus$d(?v1, ?v0))
tff(axiom203,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$'] : ( 'plus$d'(A__questionmark_v0,A__questionmark_v1) = 'plus$d'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 + ?v1) = (?v1 + ?v0))
tff(axiom204,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$(plus$(?v0), ?v1) = fun_app$(plus$(?v1), ?v0))
tff(axiom205,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:B$ ¬fun_app$h(fun_app$l(less$a, ?v0), ?v0)
tff(axiom206,axiom,
    ! [A__questionmark_v0: 'B$'] : ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ¬fun_app$e(fun_app$u(less$b, ?v0), ?v0)
tff(axiom207,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Int ¬(?v0 < ?v0)
tff(axiom208,axiom,
    ! [A__questionmark_v0: $int] : ~ $less(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:B_bool_fun$ (∃ ?v1:B$ fun_app$h(?v0, ?v1) = ∃ ?v1:B$ (fun_app$h(?v0, ?v1) ∧ ∀ ?v2:B$ (fun_app$h(fun_app$l(less$a, ?v2), ?v1) ⇒ ¬fun_app$h(?v0, ?v2))))
tff(axiom209,axiom,
    ! [A__questionmark_v0: 'B_bool_fun$'] :
      ( ? [A__questionmark_v1: 'B$'] : 'fun_app$h'(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v1: 'B$'] :
          ( 'fun_app$h'(A__questionmark_v0,A__questionmark_v1)
          & ! [A__questionmark_v2: 'B$'] :
              ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v1)
             => ~ 'fun_app$h'(A__questionmark_v0,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∃ ?v1:Nat$ fun_app$e(?v0, ?v1) = ∃ ?v1:Nat$ (fun_app$e(?v0, ?v1) ∧ ∀ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, ?v2), ?v1) ⇒ ¬fun_app$e(?v0, ?v2))))
tff(axiom210,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v1: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v1: 'Nat$'] :
          ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
          & ! [A__questionmark_v2: 'Nat$'] :
              ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v1)
             => ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) < 0) ⇒ ((?v0 < 0) ∨ (?v1 < 0)))
tff(axiom211,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),0)
     => ( $less(A__questionmark_v0,0)
        | $less(A__questionmark_v1,0) ) ) ).

%% ∀ ?v0:B_b_bool_fun_fun$ ?v1:B$ ?v2:B$ ((∀ ?v3:B$ ?v4:B$ (fun_app$h(fun_app$l(less$a, ?v3), ?v4) ⇒ fun_app$h(fun_app$l(?v0, ?v3), ?v4)) ∧ (∀ ?v3:B$ fun_app$h(fun_app$l(?v0, ?v3), ?v3) ∧ ∀ ?v3:B$ ?v4:B$ (fun_app$h(fun_app$l(?v0, ?v4), ?v3) ⇒ fun_app$h(fun_app$l(?v0, ?v3), ?v4)))) ⇒ fun_app$h(fun_app$l(?v0, ?v1), ?v2))
tff(axiom212,axiom,
    ! [A__questionmark_v0: 'B_b_bool_fun_fun$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( ! [A__questionmark_v3: 'B$',A__questionmark_v4: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$h'('fun_app$l'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: 'B$'] : 'fun_app$h'('fun_app$l'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: 'B$',A__questionmark_v4: 'B$'] :
            ( 'fun_app$h'('fun_app$l'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$h'('fun_app$l'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$h'('fun_app$l'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ (fun_app$e(fun_app$u(less$b, ?v3), ?v4) ⇒ fun_app$e(fun_app$u(?v0, ?v3), ?v4)) ∧ (∀ ?v3:Nat$ fun_app$e(fun_app$u(?v0, ?v3), ?v3) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (fun_app$e(fun_app$u(?v0, ?v4), ?v3) ⇒ fun_app$e(fun_app$u(?v0, ?v3), ?v4)))) ⇒ fun_app$e(fun_app$u(?v0, ?v1), ?v2))
tff(axiom213,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int_int_bool_fun_fun$ ?v1:Int ?v2:Int ((∀ ?v3:Int ?v4:Int ((?v3 < ?v4) ⇒ fun_app$b(fun_app$c(?v0, ?v3), ?v4)) ∧ (∀ ?v3:Int fun_app$b(fun_app$c(?v0, ?v3), ?v3) ∧ ∀ ?v3:Int ?v4:Int (fun_app$b(fun_app$c(?v0, ?v4), ?v3) ⇒ fun_app$b(fun_app$c(?v0, ?v3), ?v4)))) ⇒ fun_app$b(fun_app$c(?v0, ?v1), ?v2))
tff(axiom214,axiom,
    ! [A__questionmark_v0: 'Int_int_bool_fun_fun$',A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ! [A__questionmark_v3: $int,A__questionmark_v4: $int] :
            ( $less(A__questionmark_v3,A__questionmark_v4)
           => 'fun_app$b'('fun_app$c'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: $int] : 'fun_app$b'('fun_app$c'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int] :
            ( 'fun_app$b'('fun_app$c'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$b'('fun_app$c'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$b'('fun_app$c'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v2)) ⇒ fun_app$h(fun_app$l(less$a, ?v0), ?v2))
tff(axiom215,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom216,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 < ?v1) ∧ (?v1 < ?v2)) ⇒ (?v0 < ?v2))
tff(axiom217,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ fun_app$e(fun_app$u(less$b, ?v0), fun_app$(plus$(?v0), one$))
tff(axiom218,axiom,
    ! [A__questionmark_v0: 'Nat$'] : 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v0),'one$')) ).

%% ∀ ?v0:Int (?v0 < (?v0 + 1))
tff(axiom219,axiom,
    ! [A__questionmark_v0: $int] : $less(A__questionmark_v0,$sum(A__questionmark_v0,1)) ).

%% ∀ ?v0:Nat_set$ ?v1:Nat_set$ ?v2:Nat_set$ (plus$c(?v0, plus$c(?v1, ?v2)) = plus$c(?v1, plus$c(?v0, ?v2)))
tff(axiom220,axiom,
    ! [A__questionmark_v0: 'Nat_set$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$'] : ( 'plus$c'(A__questionmark_v0,'plus$c'(A__questionmark_v1,A__questionmark_v2)) = 'plus$c'(A__questionmark_v1,'plus$c'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int_set$ ?v1:Int_set$ ?v2:Int_set$ (plus$d(?v0, plus$d(?v1, ?v2)) = plus$d(?v1, plus$d(?v0, ?v2)))
tff(axiom221,axiom,
    ! [A__questionmark_v0: 'Int_set$',A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$'] : ( 'plus$d'(A__questionmark_v0,'plus$d'(A__questionmark_v1,A__questionmark_v2)) = 'plus$d'(A__questionmark_v1,'plus$d'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 + (?v1 + ?v2)) = (?v1 + (?v0 + ?v2)))
tff(axiom222,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : ( $sum(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v2)) = $sum(A__questionmark_v1,$sum(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$(plus$(?v0), fun_app$(plus$(?v1), ?v2)) = fun_app$(plus$(?v1), fun_app$(plus$(?v0), ?v2)))
tff(axiom223,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] : ( 'fun_app$'('plus$'(A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2)) = 'fun_app$'('plus$'(A__questionmark_v1),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:B$ ?v1:B$ (¬fun_app$h(fun_app$l(less$a, ?v0), ?v1) = (fun_app$h(fun_app$l(less$a, ?v1), ?v0) ∨ (?v0 = ?v1)))
tff(axiom224,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
        | ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬fun_app$e(fun_app$u(less$b, ?v0), ?v1) = (fun_app$e(fun_app$u(less$b, ?v1), ?v0) ∨ (?v0 = ?v1)))
tff(axiom225,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
        | ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int (¬(?v0 < ?v1) = ((?v1 < ?v0) ∨ (?v0 = ?v1)))
tff(axiom226,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ~ $less(A__questionmark_v0,A__questionmark_v1)
    <=> ( $less(A__questionmark_v1,A__questionmark_v0)
        | ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v2), ?v0)) ⇒ fun_app$h(fun_app$l(less$a, ?v2), ?v1))
tff(axiom227,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v2), ?v0)) ⇒ fun_app$e(fun_app$u(less$b, ?v2), ?v1))
tff(axiom228,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 < ?v1) ∧ (?v2 < ?v0)) ⇒ (?v2 < ?v1))
tff(axiom229,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v2,A__questionmark_v0) )
     => $less(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v0 + ?v2)) ⇒ (?v1 = ?v2))
tff(axiom230,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v0,A__questionmark_v2) )
     => ( A__questionmark_v1 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$(plus$(?v0), ?v1) = fun_app$(plus$(?v0), ?v2)) ⇒ (?v1 = ?v2))
tff(axiom231,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2) )
     => ( A__questionmark_v1 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom232,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom233,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ¬(?v0 = ?v1))
tff(axiom234,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( A__questionmark_v0 != A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), one$)), fun_app$(plus$(?v1), one$)))
tff(axiom235,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),'one$')),'fun_app$'('plus$'(A__questionmark_v1),'one$')) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ((?v0 + 1) < (?v1 + 1)))
tff(axiom236,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($sum(A__questionmark_v0,1),$sum(A__questionmark_v1,1)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) = (?v2 + ?v1)) ⇒ (?v0 = ?v2))
tff(axiom237,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = $sum(A__questionmark_v2,A__questionmark_v1) )
     => ( A__questionmark_v0 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$(plus$(?v0), ?v1) = fun_app$(plus$(?v2), ?v1)) ⇒ (?v0 = ?v2))
tff(axiom238,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1) )
     => ( A__questionmark_v0 = A__questionmark_v2 ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ¬(?v1 = ?v0))
tff(axiom239,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v1 != A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ¬(?v1 = ?v0))
tff(axiom240,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v1 != A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ¬(?v1 = ?v0))
tff(axiom241,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( A__questionmark_v1 != A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v2), ?v3)) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v2)), fun_app$(plus$(?v1), ?v3)))
tff(axiom242,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 < ?v1) ∧ (?v2 < ?v3)) ⇒ ((?v0 + ?v2) < (?v1 + ?v3)))
tff(axiom243,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v2,A__questionmark_v3) )
     => $less($sum(A__questionmark_v0,A__questionmark_v2),$sum(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v2), ?v0)), fun_app$(plus$(?v2), ?v1)))
tff(axiom244,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v0)),'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 < ?v1) ⇒ ((?v2 + ?v0) < (?v2 + ?v1)))
tff(axiom245,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($sum(A__questionmark_v2,A__questionmark_v0),$sum(A__questionmark_v2,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v2)), fun_app$(plus$(?v1), ?v2)))
tff(axiom246,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 < ?v1) ⇒ ((?v0 + ?v2) < (?v1 + ?v2)))
tff(axiom247,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($sum(A__questionmark_v0,A__questionmark_v2),$sum(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v0), ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v1), ?v2))
tff(axiom248,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2))
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) < (?v0 + ?v2)) ⇒ (?v1 < ?v2))
tff(axiom249,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v0,A__questionmark_v2))
     => $less(A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v2), ?v1)) ⇒ fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom250,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1))
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) < (?v2 + ?v1)) ⇒ (?v0 < ?v2))
tff(axiom251,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $less($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v2,A__questionmark_v1))
     => $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ fun_app$e(reduced_row_echelon_form_upt_k$(?v0), fun_app$f(nat$, 0))
tff(axiom252,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] : 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),'fun_app$f'('nat$',0)) ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ is_zero_row_upt_k$(?v0, fun_app$f(nat$, 0), ?v1)
tff(axiom253,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$'] : 'is_zero_row_upt_k$'(A__questionmark_v0,'fun_app$f'('nat$',0),A__questionmark_v1) ).

%% ∀ ?v0:B$ ?v1:B$ ((¬(?v0 = ?v1) ∧ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ false) ∧ (fun_app$h(fun_app$l(less$a, ?v1), ?v0) ⇒ false))) ⇒ false)
tff(axiom254,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((¬(?v0 = ?v1) ∧ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ false) ∧ (fun_app$e(fun_app$u(less$b, ?v1), ?v0) ⇒ false))) ⇒ false)
tff(axiom255,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ((¬(?v0 = ?v1) ∧ (((?v0 < ?v1) ⇒ false) ∧ ((?v1 < ?v0) ⇒ false))) ⇒ false)
tff(axiom256,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( $less(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( $less(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:C$ is_zero_row_upt_k$(?v1, fun_app$f(nat$, 0), ?v0)
tff(axiom257,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'C$'] : 'is_zero_row_upt_k$'(A__questionmark_v1,'fun_app$f'('nat$',0),A__questionmark_v0) ).

%% ∀ ?v0:B$ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ (¬false ⇒ fun_app$h(fun_app$l(less$a, ?v1), ?v0))) ⇒ false)
tff(axiom258,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ (¬false ⇒ fun_app$e(fun_app$u(less$b, ?v1), ?v0))) ⇒ false)
tff(axiom259,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 < ?v1) ∧ (¬false ⇒ (?v1 < ?v0))) ⇒ false)
tff(axiom260,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:B$ ?v1:B$ (¬(?v0 = ?v1) = (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∨ fun_app$h(fun_app$l(less$a, ?v1), ?v0)))
tff(axiom261,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( A__questionmark_v0 != A__questionmark_v1 )
    <=> ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        | 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(?v0 = ?v1) = (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∨ fun_app$e(fun_app$u(less$b, ?v1), ?v0)))
tff(axiom262,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 != A__questionmark_v1 )
    <=> ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        | 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int (¬(?v0 = ?v1) = ((?v0 < ?v1) ∨ (?v1 < ?v0)))
tff(axiom263,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 != A__questionmark_v1 )
    <=> ( $less(A__questionmark_v0,A__questionmark_v1)
        | $less(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:B$ ?v1:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v0)) ⇒ false)
tff(axiom264,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v0)) ⇒ false)
tff(axiom265,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 < ?v1) ∧ (?v1 < ?v0)) ⇒ false)
tff(axiom266,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ fun_app$h(fun_app$l(less$a, ?v1), ?v2)) ⇒ fun_app$h(fun_app$l(less$a, ?v0), ?v2))
tff(axiom267,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v0), ?v2))
tff(axiom268,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 < ?v1) ∧ (?v1 < ?v2)) ⇒ (?v0 < ?v2))
tff(axiom269,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int_int_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$a(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ (fun_app$a(?v1, ?v4) < fun_app$a(?v1, ?v5))))) ⇒ (?v0 < fun_app$a(?v1, ?v3)))
tff(axiom270,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_int_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$a'(A__questionmark_v1,A__questionmark_v2) )
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$a'(A__questionmark_v1,A__questionmark_v4),'fun_app$a'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$a'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:C$ ?v1:Int_c_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$v(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ less$(fun_app$v(?v1, ?v4), fun_app$v(?v1, ?v5))))) ⇒ less$(?v0, fun_app$v(?v1, ?v3)))
tff(axiom271,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'Int_c_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$v'(A__questionmark_v1,A__questionmark_v2) )
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'less$'('fun_app$v'(A__questionmark_v1,A__questionmark_v4),'fun_app$v'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less$'(A__questionmark_v0,'fun_app$v'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:B$ ?v1:Int_b_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$w(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v1, ?v4)), fun_app$w(?v1, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, ?v0), fun_app$w(?v1, ?v3)))
tff(axiom272,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'Int_b_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$w'(A__questionmark_v1,A__questionmark_v2) )
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v1,A__questionmark_v4)),'fun_app$w'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$w'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Int_nat_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$f(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v1, ?v4)), fun_app$f(?v1, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, ?v0), fun_app$f(?v1, ?v3)))
tff(axiom273,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Int_nat_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$f'(A__questionmark_v1,A__questionmark_v2) )
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v1,A__questionmark_v4)),'fun_app$f'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$f'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:C_int_fun$ ?v2:C$ ?v3:C$ (((?v0 = fun_app$x(?v1, ?v2)) ∧ (less$(?v2, ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ (fun_app$x(?v1, ?v4) < fun_app$x(?v1, ?v5))))) ⇒ (?v0 < fun_app$x(?v1, ?v3)))
tff(axiom274,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'C_int_fun$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$x'(A__questionmark_v1,A__questionmark_v2) )
        & 'less$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$x'(A__questionmark_v1,A__questionmark_v4),'fun_app$x'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$x'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:C$ ?v1:C_c_fun$ ?v2:C$ ?v3:C$ (((?v0 = fun_app$k(?v1, ?v2)) ∧ (less$(?v2, ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ less$(fun_app$k(?v1, ?v4), fun_app$k(?v1, ?v5))))) ⇒ less$(?v0, fun_app$k(?v1, ?v3)))
tff(axiom275,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C_c_fun$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$k'(A__questionmark_v1,A__questionmark_v2) )
        & 'less$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'less$'('fun_app$k'(A__questionmark_v1,A__questionmark_v4),'fun_app$k'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less$'(A__questionmark_v0,'fun_app$k'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:B$ ?v1:C_b_fun$ ?v2:C$ ?v3:C$ (((?v0 = fun_app$y(?v1, ?v2)) ∧ (less$(?v2, ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$y(?v1, ?v4)), fun_app$y(?v1, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, ?v0), fun_app$y(?v1, ?v3)))
tff(axiom276,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'C_b_fun$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$y'(A__questionmark_v1,A__questionmark_v2) )
        & 'less$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$y'(A__questionmark_v1,A__questionmark_v4)),'fun_app$y'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$y'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:C_nat_fun$ ?v2:C$ ?v3:C$ (((?v0 = fun_app$z(?v1, ?v2)) ∧ (less$(?v2, ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$z(?v1, ?v4)), fun_app$z(?v1, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, ?v0), fun_app$z(?v1, ?v3)))
tff(axiom277,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'C_nat_fun$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$z'(A__questionmark_v1,A__questionmark_v2) )
        & 'less$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$z'(A__questionmark_v1,A__questionmark_v4)),'fun_app$z'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$z'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:B_int_fun$ ?v2:B$ ?v3:B$ (((?v0 = fun_app$o(?v1, ?v2)) ∧ (fun_app$h(fun_app$l(less$a, ?v2), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ (fun_app$o(?v1, ?v4) < fun_app$o(?v1, ?v5))))) ⇒ (?v0 < fun_app$o(?v1, ?v3)))
tff(axiom278,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'B_int_fun$',A__questionmark_v2: 'B$',A__questionmark_v3: 'B$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$o'(A__questionmark_v1,A__questionmark_v2) )
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$o'(A__questionmark_v1,A__questionmark_v4),'fun_app$o'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$o'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:C$ ?v1:B_c_fun$ ?v2:B$ ?v3:B$ (((?v0 = fun_app$aa(?v1, ?v2)) ∧ (fun_app$h(fun_app$l(less$a, ?v2), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ less$(fun_app$aa(?v1, ?v4), fun_app$aa(?v1, ?v5))))) ⇒ less$(?v0, fun_app$aa(?v1, ?v3)))
tff(axiom279,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'B_c_fun$',A__questionmark_v2: 'B$',A__questionmark_v3: 'B$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$aa'(A__questionmark_v1,A__questionmark_v2) )
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'less$'('fun_app$aa'(A__questionmark_v1,A__questionmark_v4),'fun_app$aa'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less$'(A__questionmark_v0,'fun_app$aa'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_int_fun$ ?v3:Int (((?v0 < ?v1) ∧ ((fun_app$a(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ (fun_app$a(?v2, ?v4) < fun_app$a(?v2, ?v5))))) ⇒ (fun_app$a(?v2, ?v0) < ?v3))
tff(axiom280,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_int_fun$',A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$a'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$a'(A__questionmark_v2,A__questionmark_v4),'fun_app$a'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$a'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_c_fun$ ?v3:C$ (((?v0 < ?v1) ∧ ((fun_app$v(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ less$(fun_app$v(?v2, ?v4), fun_app$v(?v2, ?v5))))) ⇒ less$(fun_app$v(?v2, ?v0), ?v3))
tff(axiom281,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_c_fun$',A__questionmark_v3: 'C$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$v'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'less$'('fun_app$v'(A__questionmark_v2,A__questionmark_v4),'fun_app$v'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less$'('fun_app$v'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_b_fun$ ?v3:B$ (((?v0 < ?v1) ∧ ((fun_app$w(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v2, ?v4)), fun_app$w(?v2, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v2, ?v0)), ?v3))
tff(axiom282,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_b_fun$',A__questionmark_v3: 'B$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$w'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v2,A__questionmark_v4)),'fun_app$w'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_nat_fun$ ?v3:Nat$ (((?v0 < ?v1) ∧ ((fun_app$f(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v2, ?v4)), fun_app$f(?v2, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v2, ?v0)), ?v3))
tff(axiom283,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$f'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v2,A__questionmark_v4)),'fun_app$f'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C_int_fun$ ?v3:Int ((less$(?v0, ?v1) ∧ ((fun_app$x(?v2, ?v1) = ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ (fun_app$x(?v2, ?v4) < fun_app$x(?v2, ?v5))))) ⇒ (fun_app$x(?v2, ?v0) < ?v3))
tff(axiom284,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C_int_fun$',A__questionmark_v3: $int] :
      ( ( 'less$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$x'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$x'(A__questionmark_v2,A__questionmark_v4),'fun_app$x'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$x'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C_c_fun$ ?v3:C$ ((less$(?v0, ?v1) ∧ ((fun_app$k(?v2, ?v1) = ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ less$(fun_app$k(?v2, ?v4), fun_app$k(?v2, ?v5))))) ⇒ less$(fun_app$k(?v2, ?v0), ?v3))
tff(axiom285,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C_c_fun$',A__questionmark_v3: 'C$'] :
      ( ( 'less$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$k'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'less$'('fun_app$k'(A__questionmark_v2,A__questionmark_v4),'fun_app$k'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less$'('fun_app$k'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C_b_fun$ ?v3:B$ ((less$(?v0, ?v1) ∧ ((fun_app$y(?v2, ?v1) = ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$y(?v2, ?v4)), fun_app$y(?v2, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, fun_app$y(?v2, ?v0)), ?v3))
tff(axiom286,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C_b_fun$',A__questionmark_v3: 'B$'] :
      ( ( 'less$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$y'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$y'(A__questionmark_v2,A__questionmark_v4)),'fun_app$y'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a','fun_app$y'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:C$ ?v1:C$ ?v2:C_nat_fun$ ?v3:Nat$ ((less$(?v0, ?v1) ∧ ((fun_app$z(?v2, ?v1) = ?v3) ∧ ∀ ?v4:C$ ?v5:C$ (less$(?v4, ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$z(?v2, ?v4)), fun_app$z(?v2, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, fun_app$z(?v2, ?v0)), ?v3))
tff(axiom287,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'C$',A__questionmark_v2: 'C_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'less$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$z'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'C$',A__questionmark_v5: 'C$'] :
            ( 'less$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$z'(A__questionmark_v2,A__questionmark_v4)),'fun_app$z'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$z'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B_int_fun$ ?v3:Int ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ ((fun_app$o(?v2, ?v1) = ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ (fun_app$o(?v2, ?v4) < fun_app$o(?v2, ?v5))))) ⇒ (fun_app$o(?v2, ?v0) < ?v3))
tff(axiom288,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_int_fun$',A__questionmark_v3: $int] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & ( 'fun_app$o'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$o'(A__questionmark_v2,A__questionmark_v4),'fun_app$o'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$o'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B_c_fun$ ?v3:C$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ ((fun_app$aa(?v2, ?v1) = ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ less$(fun_app$aa(?v2, ?v4), fun_app$aa(?v2, ?v5))))) ⇒ less$(fun_app$aa(?v2, ?v0), ?v3))
tff(axiom289,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_c_fun$',A__questionmark_v3: 'C$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & ( 'fun_app$aa'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'less$'('fun_app$aa'(A__questionmark_v2,A__questionmark_v4),'fun_app$aa'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less$'('fun_app$aa'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ¬fun_app$h(fun_app$l(less$a, ?v0), ?v0)
tff(axiom290,axiom,
    ! [A__questionmark_v0: 'B$'] : ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ¬fun_app$e(fun_app$u(less$b, ?v0), ?v0)
tff(axiom291,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Int ¬(?v0 < ?v0)
tff(axiom292,axiom,
    ! [A__questionmark_v0: $int] : ~ $less(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Int ?v1:B_int_fun$ ?v2:B$ ?v3:B$ (((?v0 < fun_app$o(?v1, ?v2)) ∧ (fun_app$h(fun_app$l(less$a, ?v2), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ (fun_app$o(?v1, ?v4) < fun_app$o(?v1, ?v5))))) ⇒ (?v0 < fun_app$o(?v1, ?v3)))
tff(axiom293,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'B_int_fun$',A__questionmark_v2: 'B$',A__questionmark_v3: 'B$'] :
      ( ( $less(A__questionmark_v0,'fun_app$o'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$o'(A__questionmark_v1,A__questionmark_v4),'fun_app$o'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$o'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Nat_int_fun$ ?v2:Nat$ ?v3:Nat$ (((?v0 < fun_app$g(?v1, ?v2)) ∧ (fun_app$e(fun_app$u(less$b, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ (fun_app$g(?v1, ?v4) < fun_app$g(?v1, ?v5))))) ⇒ (?v0 < fun_app$g(?v1, ?v3)))
tff(axiom294,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat_int_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( $less(A__questionmark_v0,'fun_app$g'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$g'(A__questionmark_v1,A__questionmark_v4),'fun_app$g'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$g'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:B$ ?v1:Int_b_fun$ ?v2:Int ?v3:Int ((fun_app$h(fun_app$l(less$a, ?v0), fun_app$w(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v1, ?v4)), fun_app$w(?v1, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, ?v0), fun_app$w(?v1, ?v3)))
tff(axiom295,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'Int_b_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$w'(A__questionmark_v1,A__questionmark_v2))
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v1,A__questionmark_v4)),'fun_app$w'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$w'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:B$ ?v1:B_b_fun$ ?v2:B$ ?v3:B$ ((fun_app$h(fun_app$l(less$a, ?v0), fun_app$m(?v1, ?v2)) ∧ (fun_app$h(fun_app$l(less$a, ?v2), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$m(?v1, ?v4)), fun_app$m(?v1, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, ?v0), fun_app$m(?v1, ?v3)))
tff(axiom296,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B_b_fun$',A__questionmark_v2: 'B$',A__questionmark_v3: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$m'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$m'(A__questionmark_v1,A__questionmark_v4)),'fun_app$m'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$m'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:B$ ?v1:Nat_b_fun$ ?v2:Nat$ ?v3:Nat$ ((fun_app$h(fun_app$l(less$a, ?v0), fun_app$ab(?v1, ?v2)) ∧ (fun_app$e(fun_app$u(less$b, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$ab(?v1, ?v4)), fun_app$ab(?v1, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, ?v0), fun_app$ab(?v1, ?v3)))
tff(axiom297,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'Nat_b_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$ab'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$ab'(A__questionmark_v1,A__questionmark_v4)),'fun_app$ab'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'fun_app$ab'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Int_nat_fun$ ?v2:Int ?v3:Int ((fun_app$e(fun_app$u(less$b, ?v0), fun_app$f(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v1, ?v4)), fun_app$f(?v1, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, ?v0), fun_app$f(?v1, ?v3)))
tff(axiom298,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Int_nat_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$f'(A__questionmark_v1,A__questionmark_v2))
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v1,A__questionmark_v4)),'fun_app$f'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$f'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:B_nat_fun$ ?v2:B$ ?v3:B$ ((fun_app$e(fun_app$u(less$b, ?v0), fun_app$n(?v1, ?v2)) ∧ (fun_app$h(fun_app$l(less$a, ?v2), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$n(?v1, ?v4)), fun_app$n(?v1, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, ?v0), fun_app$n(?v1, ?v3)))
tff(axiom299,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'B_nat_fun$',A__questionmark_v2: 'B$',A__questionmark_v3: 'B$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$n'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$n'(A__questionmark_v1,A__questionmark_v4)),'fun_app$n'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$n'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_nat_fun$ ?v2:Nat$ ?v3:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), fun_app$(?v1, ?v2)) ∧ (fun_app$e(fun_app$u(less$b, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(?v1, ?v4)), fun_app$(?v1, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, ?v0), fun_app$(?v1, ?v3)))
tff(axiom300,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_nat_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$'(A__questionmark_v1,A__questionmark_v4)),'fun_app$'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'fun_app$'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int_int_fun$ ?v2:Int ?v3:Int (((?v0 < fun_app$a(?v1, ?v2)) ∧ ((?v2 < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ (fun_app$a(?v1, ?v4) < fun_app$a(?v1, ?v5))))) ⇒ (?v0 < fun_app$a(?v1, ?v3)))
tff(axiom301,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_int_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,'fun_app$a'(A__questionmark_v1,A__questionmark_v2))
        & $less(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$a'(A__questionmark_v1,A__questionmark_v4),'fun_app$a'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $less(A__questionmark_v0,'fun_app$a'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_b_fun$ ?v3:B$ (((?v0 < ?v1) ∧ (fun_app$h(fun_app$l(less$a, fun_app$w(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v2, ?v4)), fun_app$w(?v2, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, fun_app$w(?v2, ?v0)), ?v3))
tff(axiom302,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_b_fun$',A__questionmark_v3: 'B$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v2,A__questionmark_v4)),'fun_app$w'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a','fun_app$w'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_nat_fun$ ?v3:Nat$ (((?v0 < ?v1) ∧ (fun_app$e(fun_app$u(less$b, fun_app$f(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v2, ?v4)), fun_app$f(?v2, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, fun_app$f(?v2, ?v0)), ?v3))
tff(axiom303,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v2,A__questionmark_v4)),'fun_app$f'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$f'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B_int_fun$ ?v3:Int ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ ((fun_app$o(?v2, ?v1) < ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ (fun_app$o(?v2, ?v4) < fun_app$o(?v2, ?v5))))) ⇒ (fun_app$o(?v2, ?v0) < ?v3))
tff(axiom304,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_int_fun$',A__questionmark_v3: $int] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & $less('fun_app$o'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$o'(A__questionmark_v2,A__questionmark_v4),'fun_app$o'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$o'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B_b_fun$ ?v3:B$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ (fun_app$h(fun_app$l(less$a, fun_app$m(?v2, ?v1)), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$m(?v2, ?v4)), fun_app$m(?v2, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, fun_app$m(?v2, ?v0)), ?v3))
tff(axiom305,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_b_fun$',A__questionmark_v3: 'B$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a','fun_app$m'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$m'(A__questionmark_v2,A__questionmark_v4)),'fun_app$m'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a','fun_app$m'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:B_nat_fun$ ?v3:Nat$ ((fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∧ (fun_app$e(fun_app$u(less$b, fun_app$n(?v2, ?v1)), ?v3) ∧ ∀ ?v4:B$ ?v5:B$ (fun_app$h(fun_app$l(less$a, ?v4), ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$n(?v2, ?v4)), fun_app$n(?v2, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, fun_app$n(?v2, ?v0)), ?v3))
tff(axiom306,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: 'B_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b','fun_app$n'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'B$',A__questionmark_v5: 'B$'] :
            ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$n'(A__questionmark_v2,A__questionmark_v4)),'fun_app$n'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$n'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_int_fun$ ?v3:Int ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ ((fun_app$g(?v2, ?v1) < ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ (fun_app$g(?v2, ?v4) < fun_app$g(?v2, ?v5))))) ⇒ (fun_app$g(?v2, ?v0) < ?v3))
tff(axiom307,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_int_fun$',A__questionmark_v3: $int] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & $less('fun_app$g'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => $less('fun_app$g'(A__questionmark_v2,A__questionmark_v4),'fun_app$g'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$g'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_b_fun$ ?v3:B$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ (fun_app$h(fun_app$l(less$a, fun_app$ab(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ fun_app$h(fun_app$l(less$a, fun_app$ab(?v2, ?v4)), fun_app$ab(?v2, ?v5))))) ⇒ fun_app$h(fun_app$l(less$a, fun_app$ab(?v2, ?v0)), ?v3))
tff(axiom308,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_b_fun$',A__questionmark_v3: 'B$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$h'('fun_app$l'('less$a','fun_app$ab'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$h'('fun_app$l'('less$a','fun_app$ab'(A__questionmark_v2,A__questionmark_v4)),'fun_app$ab'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$h'('fun_app$l'('less$a','fun_app$ab'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_fun$ ?v3:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ (fun_app$e(fun_app$u(less$b, fun_app$(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$e(fun_app$u(less$b, ?v4), ?v5) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(?v2, ?v4)), fun_app$(?v2, ?v5))))) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(?v2, ?v0)), ?v3))
tff(axiom309,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$e'('fun_app$u'('less$b','fun_app$'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$e'('fun_app$u'('less$b','fun_app$'(A__questionmark_v2,A__questionmark_v4)),'fun_app$'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_int_fun$ ?v3:Int (((?v0 < ?v1) ∧ ((fun_app$a(?v2, ?v1) < ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 < ?v5) ⇒ (fun_app$a(?v2, ?v4) < fun_app$a(?v2, ?v5))))) ⇒ (fun_app$a(?v2, ?v0) < ?v3))
tff(axiom310,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_int_fun$',A__questionmark_v3: $int] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less('fun_app$a'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $less(A__questionmark_v4,A__questionmark_v5)
           => $less('fun_app$a'(A__questionmark_v2,A__questionmark_v4),'fun_app$a'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $less('fun_app$a'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ¬fun_app$h(fun_app$l(less$a, ?v1), ?v0))
tff(axiom311,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ¬fun_app$e(fun_app$u(less$b, ?v1), ?v0))
tff(axiom312,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ¬(?v1 < ?v0))
tff(axiom313,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ~ $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:B$ ?v1:B$ ?v2:Bool (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ((fun_app$h(fun_app$l(less$a, ?v1), ?v0) ⇒ ?v2) = true))
tff(axiom314,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$',A__questionmark_v2: tlbool] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
         => ( A__questionmark_v2 = tltrue ) )
      <=> $true ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Bool (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ((fun_app$e(fun_app$u(less$b, ?v1), ?v0) ⇒ ?v2) = true))
tff(axiom315,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: tlbool] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
         => ( A__questionmark_v2 = tltrue ) )
      <=> $true ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Bool ((?v0 < ?v1) ⇒ (((?v1 < ?v0) ⇒ ?v2) = true))
tff(axiom316,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: tlbool] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( ( $less(A__questionmark_v1,A__questionmark_v0)
         => ( A__questionmark_v2 = tltrue ) )
      <=> $true ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ∨ ((?v0 = ?v1) ∨ fun_app$h(fun_app$l(less$a, ?v1), ?v0)))
tff(axiom317,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
      | ( A__questionmark_v0 = A__questionmark_v1 )
      | 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∨ ((?v0 = ?v1) ∨ fun_app$e(fun_app$u(less$b, ?v1), ?v0)))
tff(axiom318,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
      | ( A__questionmark_v0 = A__questionmark_v1 )
      | 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ∨ ((?v0 = ?v1) ∨ (?v1 < ?v0)))
tff(axiom319,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
      | ( A__questionmark_v0 = A__questionmark_v1 )
      | $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ((?v0 = ?v1) = false))
tff(axiom320,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v0 = A__questionmark_v1 )
      <=> $false ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ((?v0 = ?v1) = false))
tff(axiom321,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v0 = A__questionmark_v1 )
      <=> $false ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ((?v0 = ?v1) = false))
tff(axiom322,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( ( A__questionmark_v0 = A__questionmark_v1 )
      <=> $false ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ ((?v1 = ?v0) = false))
tff(axiom323,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v1 = A__questionmark_v0 )
      <=> $false ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ ((?v1 = ?v0) = false))
tff(axiom324,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v1 = A__questionmark_v0 )
      <=> $false ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ ((?v1 = ?v0) = false))
tff(axiom325,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( ( A__questionmark_v1 = A__questionmark_v0 )
      <=> $false ) ) ).

%% ∀ ?v0:B$ ?v1:B$ (fun_app$h(fun_app$l(less$a, ?v0), ?v1) ⇒ (¬fun_app$h(fun_app$l(less$a, ?v1), ?v0) = true))
tff(axiom326,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v1),A__questionmark_v0)
      <=> $true ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less$b, ?v0), ?v1) ⇒ (¬fun_app$e(fun_app$u(less$b, ?v1), ?v0) = true))
tff(axiom327,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v0)
      <=> $true ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ (¬(?v1 < ?v0) = true))
tff(axiom328,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => ( ~ $less(A__questionmark_v1,A__questionmark_v0)
      <=> $true ) ) ).

%% ∀ ?v0:Nat$ ?v1:A_b_vec_c_vec$ (∀ ?v2:C$ is_zero_row_upt_k$(?v2, ?v0, ?v1) ⇒ fun_app$e(reduced_row_echelon_form_upt_k$(?v1), ?v0))
tff(axiom329,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( ! [A__questionmark_v2: 'C$'] : 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ ?v2:C$ ?v3:C$ ((fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ∧ (is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ less$(?v2, ?v3))) ⇒ is_zero_row_upt_k$(?v3, ?v1, ?v0))
tff(axiom330,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
        & 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
        & 'less$'(A__questionmark_v2,A__questionmark_v3) )
     => 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ (fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ⇒ ∀ ?v2:C$ (is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ ¬∃ ?v3:C$ (less$(?v2, ?v3) ∧ ¬is_zero_row_upt_k$(?v3, ?v1, ?v0))))
tff(axiom331,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
     => ! [A__questionmark_v2: 'C$'] :
          ( 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
         => ~ ? [A__questionmark_v3: 'C$'] :
                ( 'less$'(A__questionmark_v2,A__questionmark_v3)
                & ~ 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v1,A__questionmark_v0) ) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((¬(?v0 = ?v1) ∧ (((?v0 < ?v1) ⇒ false) ∧ ((?v1 < ?v0) ⇒ false))) ⇒ false)
tff(axiom332,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( $less(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( $less(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less$b, zero$c), ?v0) ∧ fun_app$e(fun_app$u(less$b, ?v1), ?v2)) ⇒ fun_app$e(fun_app$u(less$b, ?v1), fun_app$(plus$(?v0), ?v2)))
tff(axiom333,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v0)
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((0 < ?v0) ∧ (?v1 < ?v2)) ⇒ (?v1 < (?v0 + ?v2)))
tff(axiom334,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $less(0,A__questionmark_v0)
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less(A__questionmark_v1,$sum(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), ?v1) ∧ ∀ ?v2:Nat$ (((?v1 = fun_app$(plus$(?v0), ?v2)) ∧ ¬(?v2 = zero$c)) ⇒ false)) ⇒ false)
tff(axiom335,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( ( A__questionmark_v1 = 'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2) )
              & ( A__questionmark_v2 != 'zero$c' ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, zero$c), ?v0) ∧ fun_app$e(fun_app$u(less$b, zero$c), ?v1)) ⇒ fun_app$e(fun_app$u(less$b, zero$c), fun_app$(plus$(?v0), ?v1)))
tff(axiom336,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v0)
        & 'fun_app$e'('fun_app$u'('less$b','zero$c'),A__questionmark_v1) )
     => 'fun_app$e'('fun_app$u'('less$b','zero$c'),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int (((0 < ?v0) ∧ (0 < ?v1)) ⇒ (0 < (?v0 + ?v1)))
tff(axiom337,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(0,A__questionmark_v0)
        & $less(0,A__questionmark_v1) )
     => $less(0,$sum(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$e(fun_app$u(less$b, ?v0), zero$c) ∧ fun_app$e(fun_app$u(less$b, ?v1), zero$c)) ⇒ fun_app$e(fun_app$u(less$b, fun_app$(plus$(?v0), ?v1)), zero$c))
tff(axiom338,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'zero$c')
        & 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v1),'zero$c') )
     => 'fun_app$e'('fun_app$u'('less$b','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'zero$c') ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 < 0) ∧ (?v1 < 0)) ⇒ ((?v0 + ?v1) < 0))
tff(axiom339,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(A__questionmark_v0,0)
        & $less(A__questionmark_v1,0) )
     => $less($sum(A__questionmark_v0,A__questionmark_v1),0) ) ).

%% fun_app$e(fun_app$u(less$b, zero$c), fun_app$(plus$(one$), one$))
tff(axiom340,axiom,
    'fun_app$e'('fun_app$u'('less$b','zero$c'),'fun_app$'('plus$'('one$'),'one$')) ).

%% (0 < (1 + 1))
tff(axiom341,axiom,
    $less(0,$sum(1,1)) ).

%% ∀ ?v0:Nat_set$ (plus$c(zero$d, ?v0) = ?v0)
tff(axiom342,axiom,
    ! [A__questionmark_v0: 'Nat_set$'] : ( 'plus$c'('zero$d',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int_set$ (plus$d(zero$e, ?v0) = ?v0)
tff(axiom343,axiom,
    ! [A__questionmark_v0: 'Int_set$'] : ( 'plus$d'('zero$e',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ (fun_app$(plus$(zero$c), ?v0) = ?v0)
tff(axiom344,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('plus$'('zero$c'),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((0 + ?v0) = ?v0)
tff(axiom345,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(0,A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ (fun_app$(plus$(?v0), zero$c) = ?v0)
tff(axiom346,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('plus$'(A__questionmark_v0),'zero$c') = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((?v0 + 0) = ?v0)
tff(axiom347,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(A__questionmark_v0,0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((0 + ?v0) = ?v0)
tff(axiom348,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(0,A__questionmark_v0) = A__questionmark_v0 ) ).

%% ¬(1 < 0)
tff(axiom349,axiom,
    ~ $less(1,0) ).

%% (0 < 1)
tff(axiom350,axiom,
    $less(0,1) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ (fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ⇒ ∀ ?v2:C$ ((less$(?v2, fun_app$k(plus$a(?v2), one$a)) ∧ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ ¬is_zero_row_upt_k$(fun_app$k(plus$a(?v2), one$a), ?v1, ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v0, ?v2))), least$(uut$(?v0, ?v2)))))
tff(axiom351,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
     => ! [A__questionmark_v2: 'C$'] :
          ( ( 'less$'(A__questionmark_v2,'fun_app$k'('plus$a'(A__questionmark_v2),'one$a'))
            & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
            & ~ 'is_zero_row_upt_k$'('fun_app$k'('plus$a'(A__questionmark_v2),'one$a'),A__questionmark_v1,A__questionmark_v0) )
         => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v0,A__questionmark_v2))),'least$'('uut$'(A__questionmark_v0,A__questionmark_v2))) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ ?v2:C$ ((fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ∧ (less$(?v2, fun_app$k(plus$a(?v2), one$a)) ∧ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ ¬is_zero_row_upt_k$(fun_app$k(plus$a(?v2), one$a), ?v1, ?v0)))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v0, ?v2))), least$(uut$(?v0, ?v2))))
tff(axiom352,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'C$'] :
      ( ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
        & 'less$'(A__questionmark_v2,'fun_app$k'('plus$a'(A__questionmark_v2),'one$a'))
        & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
        & ~ 'is_zero_row_upt_k$'('fun_app$k'('plus$a'(A__questionmark_v2),'one$a'),A__questionmark_v1,A__questionmark_v0) )
     => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v0,A__questionmark_v2))),'least$'('uut$'(A__questionmark_v0,A__questionmark_v2))) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ (fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) = (∀ ?v2:C$ (is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ ¬∃ ?v3:C$ (less$(?v2, ?v3) ∧ ¬is_zero_row_upt_k$(?v3, ?v1, ?v0))) ∧ (∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v2)), least$(uua$(?v0, ?v2))) = one$c)) ∧ (∀ ?v2:C$ ((less$(?v2, fun_app$k(plus$a(?v2), one$a)) ∧ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ ¬is_zero_row_upt_k$(fun_app$k(plus$a(?v2), one$a), ?v1, ?v0))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v0, ?v2))), least$(uut$(?v0, ?v2)))) ∧ ∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ ∀ ?v3:C$ (¬(?v2 = ?v3) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v3)), least$(uua$(?v0, ?v2))) = zero$)))))))
tff(axiom353,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
    <=> ( ! [A__questionmark_v2: 'C$'] :
            ( 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
           => ~ ? [A__questionmark_v3: 'C$'] :
                  ( 'less$'(A__questionmark_v2,A__questionmark_v3)
                  & ~ 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v1,A__questionmark_v0) ) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
           => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'one$c' ) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ( 'less$'(A__questionmark_v2,'fun_app$k'('plus$a'(A__questionmark_v2),'one$a'))
              & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
              & ~ 'is_zero_row_upt_k$'('fun_app$k'('plus$a'(A__questionmark_v2),'one$a'),A__questionmark_v1,A__questionmark_v0) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v0,A__questionmark_v2))),'least$'('uut$'(A__questionmark_v0,A__questionmark_v2))) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
           => ! [A__questionmark_v3: 'C$'] :
                ( ( A__questionmark_v2 != A__questionmark_v3 )
               => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v3)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'zero$' ) ) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:A_b_vec_c_vec$ ((∀ ?v2:C$ (is_zero_row_upt_k$(?v2, ?v0, ?v1) ⇒ ¬∃ ?v3:C$ (less$(?v2, ?v3) ∧ ¬is_zero_row_upt_k$(?v3, ?v0, ?v1))) ∧ (∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v0, ?v1) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v1), ?v2)), least$(uua$(?v1, ?v2))) = one$c)) ∧ (∀ ?v2:C$ ((less$(?v2, fun_app$k(plus$a(?v2), one$a)) ∧ (¬is_zero_row_upt_k$(?v2, ?v0, ?v1) ∧ ¬is_zero_row_upt_k$(fun_app$k(plus$a(?v2), one$a), ?v0, ?v1))) ⇒ fun_app$h(fun_app$l(less$a, least$(uua$(?v1, ?v2))), least$(uut$(?v1, ?v2)))) ∧ ∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v0, ?v1) ⇒ ∀ ?v3:C$ (¬(?v2 = ?v3) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v1), ?v3)), least$(uua$(?v1, ?v2))) = zero$)))))) ⇒ fun_app$e(reduced_row_echelon_form_upt_k$(?v1), ?v0))
tff(axiom354,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( ( ! [A__questionmark_v2: 'C$'] :
            ( 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
           => ~ ? [A__questionmark_v3: 'C$'] :
                  ( 'less$'(A__questionmark_v2,A__questionmark_v3)
                  & ~ 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v0,A__questionmark_v1) ) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
           => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2)),'least$'('uua$'(A__questionmark_v1,A__questionmark_v2))) = 'one$c' ) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ( 'less$'(A__questionmark_v2,'fun_app$k'('plus$a'(A__questionmark_v2),'one$a'))
              & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
              & ~ 'is_zero_row_upt_k$'('fun_app$k'('plus$a'(A__questionmark_v2),'one$a'),A__questionmark_v0,A__questionmark_v1) )
           => 'fun_app$h'('fun_app$l'('less$a','least$'('uua$'(A__questionmark_v1,A__questionmark_v2))),'least$'('uut$'(A__questionmark_v1,A__questionmark_v2))) )
        & ! [A__questionmark_v2: 'C$'] :
            ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
           => ! [A__questionmark_v3: 'C$'] :
                ( ( A__questionmark_v2 != A__questionmark_v3 )
               => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3)),'least$'('uua$'(A__questionmark_v1,A__questionmark_v2))) = 'zero$' ) ) ) )
     => 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ ?v2:Nat$ (is_zero_row$(?v0, ?v1) ⇒ is_zero_row_upt_k$(?v0, ?v2, ?v1))
tff(axiom355,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$',A__questionmark_v2: 'Nat$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
     => 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:B$ ?v1:B_bool_fun$ (fun_app$h(fun_app$l(less$a, ?v0), least$(?v1)) ⇒ ¬fun_app$h(?v1, ?v0))
tff(axiom356,axiom,
    ! [A__questionmark_v0: 'B$',A__questionmark_v1: 'B_bool_fun$'] :
      ( 'fun_app$h'('fun_app$l'('less$a',A__questionmark_v0),'least$'(A__questionmark_v1))
     => ~ 'fun_app$h'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (fun_app$e(fun_app$u(less$b, ?v0), least$a(?v1)) ⇒ ¬fun_app$e(?v1, ?v0))
tff(axiom357,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( 'fun_app$e'('fun_app$u'('less$b',A__questionmark_v0),'least$a'(A__questionmark_v1))
     => ~ 'fun_app$e'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ (fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ⇒ ∀ ?v2:C$ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ ∀ ?v3:C$ (¬(?v2 = ?v3) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v3)), least$(uua$(?v0, ?v2))) = zero$))))
tff(axiom358,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
     => ! [A__questionmark_v2: 'C$'] :
          ( ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
         => ! [A__questionmark_v3: 'C$'] :
              ( ( A__questionmark_v2 != A__questionmark_v3 )
             => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v3)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'zero$' ) ) ) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ ?v1:Nat$ ?v2:C$ ?v3:C$ ((fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ?v1) ∧ (¬is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ ¬(?v2 = ?v3))) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v0), ?v3)), least$(uua$(?v0, ?v2))) = zero$))
tff(axiom359,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'C$',A__questionmark_v3: 'C$'] :
      ( ( 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
        & ~ 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
        & ( A__questionmark_v2 != A__questionmark_v3 ) )
     => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v0),A__questionmark_v3)),'least$'('uua$'(A__questionmark_v0,A__questionmark_v2))) = 'zero$' ) ) ).

%% ∀ ?v0:Int (((?v0 + ?v0) = 0) = (?v0 = 0))
tff(axiom360,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v0) = 0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% (0 < 1)
tff(axiom361,axiom,
    $less(0,1) ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ (is_zero_row_upt_k$(?v0, ncols$(?v1), ?v1) = ∀ ?v2:B$ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v1), ?v0)), ?v2) = zero$))
tff(axiom362,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( 'is_zero_row_upt_k$'(A__questionmark_v0,'ncols$'(A__questionmark_v1),A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'B$'] : ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v1),A__questionmark_v0)),A__questionmark_v2) = 'zero$' ) ) ).

%% ∀ ?v0:Int ?v1:Int_set$ ?v2:Int ?v3:Int_set$ ((member$b(?v0, ?v1) ∧ member$b(?v2, ?v3)) ⇒ member$b((?v0 + ?v2), plus$d(?v1, ?v3)))
tff(axiom363,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_set$',A__questionmark_v2: $int,A__questionmark_v3: 'Int_set$'] :
      ( ( 'member$b'(A__questionmark_v0,A__questionmark_v1)
        & 'member$b'(A__questionmark_v2,A__questionmark_v3) )
     => 'member$b'($sum(A__questionmark_v0,A__questionmark_v2),'plus$d'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Num$ ?v1:Num_set$ ?v2:Num$ ?v3:Num_set$ ((member$(?v0, ?v1) ∧ member$(?v2, ?v3)) ⇒ member$(plus$e(?v0, ?v2), plus$f(?v1, ?v3)))
tff(axiom364,axiom,
    ! [A__questionmark_v0: 'Num$',A__questionmark_v1: 'Num_set$',A__questionmark_v2: 'Num$',A__questionmark_v3: 'Num_set$'] :
      ( ( 'member$'(A__questionmark_v0,A__questionmark_v1)
        & 'member$'(A__questionmark_v2,A__questionmark_v3) )
     => 'member$'('plus$e'(A__questionmark_v0,A__questionmark_v2),'plus$f'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_set$ ?v2:Nat$ ?v3:Nat_set$ ((member$a(?v0, ?v1) ∧ member$a(?v2, ?v3)) ⇒ member$a(fun_app$(plus$(?v0), ?v2), plus$c(?v1, ?v3)))
tff(axiom365,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat_set$'] :
      ( ( 'member$a'(A__questionmark_v0,A__questionmark_v1)
        & 'member$a'(A__questionmark_v2,A__questionmark_v3) )
     => 'member$a'('fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2),'plus$c'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ¬(1 < 1)
tff(axiom366,axiom,
    ~ $less(1,1) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) + ?v2) = (?v0 + (?v1 + ?v2)))
tff(axiom367,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : ( $sum($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = $sum(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int_set$ ?v2:Int_set$ ((member$b(?v0, plus$d(?v1, ?v2)) ∧ ∀ ?v3:Int ?v4:Int (((?v0 = (?v3 + ?v4)) ∧ (member$b(?v3, ?v1) ∧ member$b(?v4, ?v2))) ⇒ false)) ⇒ false)
tff(axiom368,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_set$',A__questionmark_v2: 'Int_set$'] :
      ( ( 'member$b'(A__questionmark_v0,'plus$d'(A__questionmark_v1,A__questionmark_v2))
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int] :
            ( ( ( A__questionmark_v0 = $sum(A__questionmark_v3,A__questionmark_v4) )
              & 'member$b'(A__questionmark_v3,A__questionmark_v1)
              & 'member$b'(A__questionmark_v4,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Num$ ?v1:Num_set$ ?v2:Num_set$ ((member$(?v0, plus$f(?v1, ?v2)) ∧ ∀ ?v3:Num$ ?v4:Num$ (((?v0 = plus$e(?v3, ?v4)) ∧ (member$(?v3, ?v1) ∧ member$(?v4, ?v2))) ⇒ false)) ⇒ false)
tff(axiom369,axiom,
    ! [A__questionmark_v0: 'Num$',A__questionmark_v1: 'Num_set$',A__questionmark_v2: 'Num_set$'] :
      ( ( 'member$'(A__questionmark_v0,'plus$f'(A__questionmark_v1,A__questionmark_v2))
        & ! [A__questionmark_v3: 'Num$',A__questionmark_v4: 'Num$'] :
            ( ( ( A__questionmark_v0 = 'plus$e'(A__questionmark_v3,A__questionmark_v4) )
              & 'member$'(A__questionmark_v3,A__questionmark_v1)
              & 'member$'(A__questionmark_v4,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_set$ ?v2:Nat_set$ ((member$a(?v0, plus$c(?v1, ?v2)) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (((?v0 = fun_app$(plus$(?v3), ?v4)) ∧ (member$a(?v3, ?v1) ∧ member$a(?v4, ?v2))) ⇒ false)) ⇒ false)
tff(axiom370,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_set$',A__questionmark_v2: 'Nat_set$'] :
      ( ( 'member$a'(A__questionmark_v0,'plus$c'(A__questionmark_v1,A__questionmark_v2))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$'('plus$'(A__questionmark_v3),A__questionmark_v4) )
              & 'member$a'(A__questionmark_v3,A__questionmark_v1)
              & 'member$a'(A__questionmark_v4,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:C$ ?v1:A_b_vec_c_vec$ (is_zero_row$(?v0, ?v1) = is_zero_row_upt_k$(?v0, ncols$(?v1), ?v1))
tff(axiom371,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'A_b_vec_c_vec$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
    <=> 'is_zero_row_upt_k$'(A__questionmark_v0,'ncols$'(A__questionmark_v1),A__questionmark_v1) ) ).

%% ∀ ?v0:A_b_vec_c_vec$ (reduced_row_echelon_form$(?v0) = fun_app$e(reduced_row_echelon_form_upt_k$(?v0), ncols$(?v0)))
tff(axiom372,axiom,
    ! [A__questionmark_v0: 'A_b_vec_c_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
    <=> 'fun_app$e'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),'ncols$'(A__questionmark_v0)) ) ).

%% ¬(0 < 0)
tff(axiom373,axiom,
    ~ $less(0,0) ).

%% ∀ ?v0:Nat$ (¬(fun_app$g(of_nat$, ?v0) = 0) = (0 < fun_app$g(of_nat$, ?v0)))
tff(axiom374,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 0 )
    <=> $less(0,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((0 < (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1))) = ((0 < fun_app$g(of_nat$, ?v0)) ∨ (0 < fun_app$g(of_nat$, ?v1))))
tff(axiom375,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less(0,$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))
    <=> ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
        | $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) = 0) = ((fun_app$g(of_nat$, ?v0) = 0) ∧ (fun_app$g(of_nat$, ?v1) = 0)))
tff(axiom376,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) = 0 )
    <=> ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
        & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) < 1) = (fun_app$g(of_nat$, ?v0) = 0))
tff(axiom377,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),1)
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ (¬(fun_app$g(of_nat$, ?v0) = 0) = (0 < fun_app$g(of_nat$, ?v0)))
tff(axiom378,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 0 )
    <=> $less(0,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) + 0) = fun_app$g(of_nat$, ?v0))
tff(axiom379,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),0) = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_bool_fun$ (fun_app$e(?v0, fun_app$f(nat$, 0)) ⇒ (fun_app$g(of_nat$, least$a(?v0)) = 0))
tff(axiom380,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0))
     => ( 'fun_app$g'('of_nat$','least$a'(A__questionmark_v0)) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) < 0) = false)
tff(axiom381,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),0)
    <=> $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) < (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2))) = (fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v2)))
tff(axiom382,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ ((fun_app$g(of_nat$, ?v2) + fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v3)))) ⇒ (fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v3)))
tff(axiom383,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ( $sum('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v1)) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v3)) ) )
     => $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v2) + fun_app$g(of_nat$, ?v1))))
tff(axiom384,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v1))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + fun_app$g(of_nat$, ?v2))))
tff(axiom385,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) < (fun_app$g(of_nat$, ?v1) + fun_app$g(of_nat$, ?v2))))
tff(axiom386,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)),$sum('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ¬((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) < fun_app$g(of_nat$, ?v1))
tff(axiom387,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ~ $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),'fun_app$g'('of_nat$',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ¬((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) < fun_app$g(of_nat$, ?v0))
tff(axiom388,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ~ $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),'fun_app$g'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v3))) ⇒ ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) < (fun_app$g(of_nat$, ?v1) + fun_app$g(of_nat$, ?v3))))
tff(axiom389,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v3)) )
     => $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)),$sum('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v3))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) < fun_app$g(of_nat$, ?v2)) ⇒ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v2)))
tff(axiom390,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),'fun_app$g'('of_nat$',A__questionmark_v2))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) = ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∨ (fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v0))))
tff(axiom391,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 'fun_app$g'('of_nat$',A__questionmark_v1) )
    <=> ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        | $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v0)) ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v0))
tff(axiom392,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ¬(fun_app$g(of_nat$, ?v1) = fun_app$g(of_nat$, ?v0)))
tff(axiom393,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$g'('of_nat$',A__questionmark_v1) != 'fun_app$g'('of_nat$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ¬(fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom394,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v0)) ⇒ false)
tff(axiom395,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v0))
     => $false ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (∀ ?v3:Nat$ ((fun_app$g(of_nat$, ?v3) < fun_app$g(of_nat$, ?v2)) ⇒ fun_app$e(?v0, ?v3)) ⇒ fun_app$e(?v0, ?v2)) ⇒ fun_app$e(?v0, ?v1))
tff(axiom396,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ! [A__questionmark_v3: 'Nat$'] :
              ( $less('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v2))
             => 'fun_app$e'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (¬fun_app$e(?v0, ?v2) ⇒ ∃ ?v3:Nat$ ((fun_app$g(of_nat$, ?v3) < fun_app$g(of_nat$, ?v2)) ∧ ¬fun_app$e(?v0, ?v3))) ⇒ fun_app$e(?v0, ?v1))
tff(axiom397,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v2)
         => ? [A__questionmark_v3: 'Nat$'] :
              ( $less('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v2))
              & ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v3) ) )
     => 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((¬(fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) ∧ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v0)) ⇒ false))) ⇒ false)
tff(axiom398,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 'fun_app$g'('of_nat$',A__questionmark_v1) )
        & ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
         => $false )
        & ( $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v0))
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ((((fun_app$g(of_nat$, ?v0) = 0) ⇒ false) ∧ (¬(fun_app$g(of_nat$, ?v0) = 0) ⇒ false)) ⇒ false)
tff(axiom399,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 0 )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ∃ ?v2:Nat$ ((0 < fun_app$g(of_nat$, ?v2)) ∧ ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) = fun_app$g(of_nat$, ?v1))))
tff(axiom400,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ? [A__questionmark_v2: 'Nat$'] :
          ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v2))
          & ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$e(?v0, fun_app$f(nat$, 0)) ∧ ∀ ?v2:Nat$ (((0 < fun_app$g(of_nat$, ?v2)) ∧ ¬fun_app$e(?v0, ?v2)) ⇒ ∃ ?v3:Nat$ ((fun_app$g(of_nat$, ?v3) < fun_app$g(of_nat$, ?v2)) ∧ ¬fun_app$e(?v0, ?v3)))) ⇒ fun_app$e(?v0, ?v1))
tff(axiom401,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v2))
              & ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) )
           => ? [A__questionmark_v3: 'Nat$'] :
                ( $less('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v2))
                & ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v3) ) ) )
     => 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) = fun_app$g(of_nat$, ?v0)) ⇒ (fun_app$g(of_nat$, ?v1) = 0))
tff(axiom402,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) = 'fun_app$g'('of_nat$',A__questionmark_v0) )
     => ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ¬(fun_app$g(of_nat$, ?v1) = 0))
tff(axiom403,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$g'('of_nat$',A__questionmark_v1) != 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) < 0) ⇒ false)
tff(axiom404,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),0)
     => $false ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, ?v0) < 0)
tff(axiom405,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ (¬(0 < fun_app$g(of_nat$, ?v0)) = (fun_app$g(of_nat$, ?v0) = 0))
tff(axiom406,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ~ $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ (((fun_app$g(of_nat$, ?v0) = 0) ⇒ false) ⇒ (0 < fun_app$g(of_nat$, ?v0)))
tff(axiom407,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
       => $false )
     => $less(0,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, ?v0) < 0)
tff(axiom408,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ ((0 + fun_app$g(of_nat$, ?v0)) = fun_app$g(of_nat$, ?v0))
tff(axiom409,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum(0,'fun_app$g'('of_nat$',A__questionmark_v0)) = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ (fun_app$e(fun_app$u(?v0, ?v3), ?v4) = fun_app$e(fun_app$u(?v0, ?v4), ?v3)) ∧ (∀ ?v3:Nat$ fun_app$e(fun_app$u(?v0, ?v3), fun_app$f(nat$, 0)) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (fun_app$e(fun_app$u(?v0, ?v3), ?v4) ⇒ fun_app$e(fun_app$u(?v0, ?v3), fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + fun_app$g(of_nat$, ?v4))))))) ⇒ fun_app$e(fun_app$u(?v0, ?v1), ?v2))
tff(axiom410,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)
          <=> 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3) )
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),'fun_app$f'('nat$',0))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v4)))) ) )
     => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = (?v0 + ?v1)) = (?v1 = 0))
tff(axiom411,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v0,A__questionmark_v1) )
    <=> ( A__questionmark_v1 = 0 ) ) ).

%% ∀ ?v0:Nat$ (fun_app$(plus$(?v0), zero$c) = ?v0)
tff(axiom412,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('plus$'(A__questionmark_v0),'zero$c') = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((?v0 + 0) = ?v0)
tff(axiom413,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(A__questionmark_v0,0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ((?v0 < ?v0) = false)
tff(axiom414,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v0)
    <=> $false ) ).

%% ∀ ?v0:C$ ?v1:Nat$ ?v2:A_b_vec_c_vec$ (is_zero_row_upt_k$(?v0, ?v1, ?v2) = ∀ ?v3:B$ ((fun_app$g(of_nat$, fun_app$n(to_nat$, ?v3)) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v2), ?v0)), ?v3) = zero$)))
tff(axiom415,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_b_vec_c_vec$'] :
      ( 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2)
    <=> ! [A__questionmark_v3: 'B$'] :
          ( $less('fun_app$g'('of_nat$','fun_app$n'('to_nat$',A__questionmark_v3)),'fun_app$g'('of_nat$',A__questionmark_v1))
         => ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v0)),A__questionmark_v3) = 'zero$' ) ) ) ).

%% (fun_app$a(dbl_inc$, 0) = 1)
tff(axiom416,axiom,
    'fun_app$a'('dbl_inc$',0) = 1 ).

%% ∀ ?v0:Int (fun_app$a(dbl_inc$, ?v0) = ((?v0 + ?v0) + 1))
tff(axiom417,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$a'('dbl_inc$',A__questionmark_v0) = $sum($sum(A__questionmark_v0,A__questionmark_v0),1) ) ).

%% ∀ ?v0:C$ ?v1:Nat$ ?v2:A_b_vec_c_vec$ ((is_zero_row_upt_k$(?v0, ?v1, ?v2) ∧ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v2), ?v0)), fun_app$ab(from_nat$, ?v1)) = zero$)) ⇒ is_zero_row_upt_k$(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1)), ?v2))
tff(axiom418,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_b_vec_c_vec$'] :
      ( ( 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2)
        & ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v0)),'fun_app$ab'('from_nat$',A__questionmark_v1)) = 'zero$' ) )
     => 'is_zero_row_upt_k$'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)),A__questionmark_v2) ) ).

%% ∀ ?v0:C$ ?v1:Nat$ ?v2:A_b_vec_c_vec$ ((¬is_zero_row_upt_k$(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1)), ?v2) ∧ ∀ ?v3:C$ (fun_app$i(vec_nth$(fun_app$j(vec_nth$a(?v2), ?v3)), fun_app$ab(from_nat$, ?v1)) = zero$)) ⇒ ¬is_zero_row_upt_k$(?v0, ?v1, ?v2))
tff(axiom419,axiom,
    ! [A__questionmark_v0: 'C$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_b_vec_c_vec$'] :
      ( ( ~ 'is_zero_row_upt_k$'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)),A__questionmark_v2)
        & ! [A__questionmark_v3: 'C$'] : ( 'fun_app$i'('vec_nth$'('fun_app$j'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3)),'fun_app$ab'('from_nat$',A__questionmark_v1)) = 'zero$' ) )
     => ~ 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$g(of_nat$, ?v0)) = (0 < fun_app$g(of_nat$, ?v0)))
tff(axiom420,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
    <=> $less(0,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((0 < fun_app$g(of_nat$, ?v0)) ∧ (0 < fun_app$g(of_nat$, ?v1))) ⇒ (num_of_nat$(fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = plus$e(num_of_nat$(?v0), num_of_nat$(?v1))))
tff(axiom421,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
        & $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) )
     => ( 'num_of_nat$'('fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = 'plus$e'('num_of_nat$'(A__questionmark_v0),'num_of_nat$'(A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) = (fun_app$g(of_nat$, ?v1) + 1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom422,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) = (fun_app$g(of_nat$, ?v1) + 1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom423,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom424,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) < (fun_app$g(of_nat$, ?v1) + 1)) = (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom425,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ((fun_app$g(of_nat$, ?v0) + 1) < (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom426,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom427,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) + (fun_app$g(of_nat$, ?v1) + 1)) = ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) + 1))
tff(axiom428,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)) = $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),1) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) = 0) = (fun_app$g(of_nat$, ?v0) = 0))
tff(axiom429,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((0 = fun_app$g(of_nat$, ?v0)) = (0 = fun_app$g(of_nat$, ?v0)))
tff(axiom430,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 0 = 'fun_app$g'('of_nat$',A__questionmark_v0) )
    <=> ( 0 = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ) ).

%% (fun_app$g(of_nat$, fun_app$f(nat$, 0)) = 0)
tff(axiom431,axiom,
    'fun_app$g'('of_nat$','fun_app$f'('nat$',0)) = 0 ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom432,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$(of_nat$a, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = fun_app$(plus$(fun_app$(of_nat$a, ?v0)), fun_app$(of_nat$a, ?v1)))
tff(axiom433,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$'('of_nat$a','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = 'fun_app$'('plus$'('fun_app$'('of_nat$a',A__questionmark_v0)),'fun_app$'('of_nat$a',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))
tff(axiom434,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ (0 < (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom435,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less(0,$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) < (0 + 1)) = (fun_app$g(of_nat$, ?v0) = 0))
tff(axiom436,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum(0,1))
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) = 1) = (fun_app$g(of_nat$, ?v0) = 1))
tff(axiom437,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 1 )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% ∀ ?v0:Nat$ ((1 = fun_app$g(of_nat$, ?v0)) = (fun_app$g(of_nat$, ?v0) = 1))
tff(axiom438,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 1 = 'fun_app$g'('of_nat$',A__questionmark_v0) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% (fun_app$g(of_nat$, fun_app$f(nat$, 1)) = 1)
tff(axiom439,axiom,
    'fun_app$g'('of_nat$','fun_app$f'('nat$',1)) = 1 ).

%% ∀ ?v0:Nat$ (fun_app$(of_nat$a, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) = fun_app$(plus$(one$), fun_app$(of_nat$a, ?v0)))
tff(axiom440,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('of_nat$a','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) = 'fun_app$'('plus$'('one$'),'fun_app$'('of_nat$a',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) = (1 + fun_app$g(of_nat$, ?v0)))
tff(axiom441,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) = $sum(1,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) = ∃ ?v2:Nat$ (?v1 = (?v0 + fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))))))
tff(axiom442,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v2: 'Nat$'] : ( A__questionmark_v1 = $sum(A__questionmark_v0,'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1)))) ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) = 0)
tff(axiom443,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) != 0 ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom444,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) != $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) = (fun_app$g(of_nat$, ?v1) + 1)) ⇒ (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom445,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
     => ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) + fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) + (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom446,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1)) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) + fun_app$g(of_nat$, ?v1)) = ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) + 1))
tff(axiom447,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1)) = $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + fun_app$g(of_nat$, ?v2))) ⇒ ((fun_app$g(of_nat$, ?v0) + 1) = (fun_app$g(of_nat$, ?v1) + (fun_app$g(of_nat$, ?v2) + 1))))
tff(axiom448,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2)) )
     => ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),$sum('fun_app$g'('of_nat$',A__questionmark_v2),1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (((fun_app$g(of_nat$, ?v1) = (fun_app$g(of_nat$, ?v0) + 1)) ⇒ false) ∧ ∀ ?v2:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v2)) ∧ (fun_app$g(of_nat$, ?v1) = (fun_app$g(of_nat$, ?v2) + 1))) ⇒ false))) ⇒ false)
tff(axiom449,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ( ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) )
         => $false )
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2))
              & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum('fun_app$g'('of_nat$',A__questionmark_v2),1) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom450,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((((fun_app$g(of_nat$, ?v0) + 1) < fun_app$g(of_nat$, ?v1)) ∧ ∀ ?v2:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v2)) ∧ (fun_app$g(of_nat$, ?v1) = (fun_app$g(of_nat$, ?v2) + 1))) ⇒ false)) ⇒ false)
tff(axiom451,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2))
              & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum('fun_app$g'('of_nat$',A__questionmark_v2),1) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ ¬((fun_app$g(of_nat$, ?v0) + 1) = fun_app$g(of_nat$, ?v1))) ⇒ ((fun_app$g(of_nat$, ?v0) + 1) < fun_app$g(of_nat$, ?v1)))
tff(axiom452,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) != 'fun_app$g'('of_nat$',A__questionmark_v1) ) )
     => $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1)) ∧ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) ⇒ false))) ⇒ false)
tff(axiom453,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
        & ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
         => $false )
        & ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom454,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < (fun_app$g(of_nat$, ?v0) + 1)) ∧ fun_app$e(?v1, ?v2)) = (fun_app$e(?v1, ?v0) ∨ ∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v0)) ∧ fun_app$e(?v1, ?v2))))
tff(axiom455,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$g'('of_nat$',A__questionmark_v2),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))
          & 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$e'(A__questionmark_v1,A__questionmark_v0)
        | ? [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v0))
            & 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1)) = ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∨ (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1))))
tff(axiom456,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
    <=> ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v1) < (fun_app$g(of_nat$, ?v0) + 1)))
tff(axiom457,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v1),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∀ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < (fun_app$g(of_nat$, ?v0) + 1)) ⇒ fun_app$e(?v1, ?v2)) = (fun_app$e(?v1, ?v0) ∧ ∀ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v0)) ⇒ fun_app$e(?v1, ?v2))))
tff(axiom458,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$g'('of_nat$',A__questionmark_v2),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))
         => 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$e'(A__questionmark_v1,A__questionmark_v0)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v0))
           => 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) < fun_app$g(of_nat$, ?v1)) = ∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v1) = (fun_app$g(of_nat$, ?v2) + 1)) ∧ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v2))))
tff(axiom459,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> ? [A__questionmark_v2: 'Nat$'] :
          ( ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum('fun_app$g'('of_nat$',A__questionmark_v2),1) )
          & $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((¬(fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1))) ⇒ (fun_app$g(of_nat$, ?v1) = fun_app$g(of_nat$, ?v0)))
tff(axiom460,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)) )
     => ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) < (fun_app$g(of_nat$, ?v1) + 1)) ⇒ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom461,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v2))) ⇒ ((fun_app$g(of_nat$, ?v0) + 1) < fun_app$g(of_nat$, ?v2)))
tff(axiom462,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2)) )
     => $less($sum('fun_app$g'('of_nat$',A__questionmark_v0),1),'fun_app$g'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_bool_fun_fun$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ fun_app$e(fun_app$u(?v2, ?v3), fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1))) ∧ ∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ (((fun_app$g(of_nat$, ?v3) < fun_app$g(of_nat$, ?v4)) ∧ ((fun_app$g(of_nat$, ?v4) < fun_app$g(of_nat$, ?v5)) ∧ (fun_app$e(fun_app$u(?v2, ?v3), ?v4) ∧ fun_app$e(fun_app$u(?v2, ?v4), ?v5)))) ⇒ fun_app$e(fun_app$u(?v2, ?v3), ?v5)))) ⇒ fun_app$e(fun_app$u(?v2, ?v0), ?v1))
tff(axiom463,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$e'('fun_app$u'(A__questionmark_v2,A__questionmark_v3),'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1)))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( $less('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v4))
              & $less('fun_app$g'('of_nat$',A__questionmark_v4),'fun_app$g'('of_nat$',A__questionmark_v5))
              & 'fun_app$e'('fun_app$u'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)
              & 'fun_app$e'('fun_app$u'(A__questionmark_v2,A__questionmark_v4),A__questionmark_v5) )
           => 'fun_app$e'('fun_app$u'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5) ) )
     => 'fun_app$e'('fun_app$u'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ ((fun_app$g(of_nat$, ?v1) = (fun_app$g(of_nat$, ?v3) + 1)) ⇒ fun_app$e(?v2, ?v3)) ∧ ∀ ?v3:Nat$ (((fun_app$g(of_nat$, ?v3) < fun_app$g(of_nat$, ?v1)) ∧ fun_app$e(?v2, fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1)))) ⇒ fun_app$e(?v2, ?v3)))) ⇒ fun_app$e(?v2, ?v0))
tff(axiom464,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum('fun_app$g'('of_nat$',A__questionmark_v3),1) )
           => 'fun_app$e'(A__questionmark_v2,A__questionmark_v3) )
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $less('fun_app$g'('of_nat$',A__questionmark_v3),'fun_app$g'('of_nat$',A__questionmark_v1))
              & 'fun_app$e'(A__questionmark_v2,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1))) )
           => 'fun_app$e'(A__questionmark_v2,A__questionmark_v3) ) )
     => 'fun_app$e'(A__questionmark_v2,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ((fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1))))
tff(axiom465,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ( $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
      <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Int ((fun_app$g(of_nat$, ?v0) + (fun_app$g(of_nat$, ?v1) + ?v2)) = (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) + ?v2))
tff(axiom466,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $int] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),A__questionmark_v2)) = $sum('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ (¬(fun_app$g(of_nat$, ?v0) = 0) ⇒ ∃ ?v1:Nat$ (fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom467,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 0 )
     => ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom468,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ((0 = (fun_app$g(of_nat$, ?v0) + 1)) ⇒ false)
tff(axiom469,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 0 = $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) )
     => $false ) ).

%% ∀ ?v0:Nat$ (((fun_app$g(of_nat$, ?v0) + 1) = 0) ⇒ false)
tff(axiom470,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = 0 )
     => $false ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$e(?v0, ?v1) ∧ ∀ ?v2:Nat$ (fun_app$e(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))) ⇒ fun_app$e(?v0, ?v2))) ⇒ fun_app$e(?v0, fun_app$f(nat$, 0)))
tff(axiom471,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1)))
           => 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) ) )
     => 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0)) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$e(fun_app$u(?v0, ?v3), fun_app$f(nat$, 0)) ∧ (∀ ?v3:Nat$ fun_app$e(fun_app$u(?v0, fun_app$f(nat$, 0)), fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1))) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (fun_app$e(fun_app$u(?v0, ?v3), ?v4) ⇒ fun_app$e(fun_app$u(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1))), fun_app$f(nat$, (fun_app$g(of_nat$, ?v4) + 1)))))) ⇒ fun_app$e(fun_app$u(?v0, ?v1), ?v2))
tff(axiom472,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),'fun_app$f'('nat$',0))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$e'('fun_app$u'(A__questionmark_v0,'fun_app$f'('nat$',0)),'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1)))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$e'('fun_app$u'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1))),'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v4),1))) ) )
     => 'fun_app$e'('fun_app$u'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$e(?v0, fun_app$f(nat$, 0)) ∧ ∀ ?v2:Nat$ (fun_app$e(?v0, ?v2) ⇒ fun_app$e(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))))) ⇒ fun_app$e(?v0, ?v1))
tff(axiom473,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v2)
           => 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1))) ) )
     => 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ((((fun_app$g(of_nat$, ?v0) = 0) ⇒ false) ∧ ∀ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)) ⇒ false)) ⇒ false)
tff(axiom474,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)) ⇒ ¬(fun_app$g(of_nat$, ?v0) = 0))
tff(axiom475,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
     => ( 'fun_app$g'('of_nat$',A__questionmark_v0) != 0 ) ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom476,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ¬((fun_app$g(of_nat$, ?v0) + 1) = 0)
tff(axiom477,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) != 0 ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom478,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% (fun_app$g(of_nat$, fun_app$f(nat$, 0)) = 0)
tff(axiom479,axiom,
    'fun_app$g'('of_nat$','fun_app$f'('nat$',0)) = 0 ).

%% (fun_app$g(of_nat$, fun_app$f(nat$, 1)) = 1)
tff(axiom480,axiom,
    'fun_app$g'('of_nat$','fun_app$f'('nat$',1)) = 1 ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom481,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))
tff(axiom482,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))
tff(axiom483,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom484,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom485,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom486,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$g(of_nat$, ?v0) < 0)
tff(axiom487,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom488,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ (fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)))
tff(axiom489,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int (((0 < ?v0) ∧ ∀ ?v1:Nat$ (((?v0 = fun_app$g(of_nat$, ?v1)) ∧ (0 < fun_app$g(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom490,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $less(0,A__questionmark_v0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
              & $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ((0 < ?v0) ⇒ ∃ ?v1:Nat$ ((0 < fun_app$g(of_nat$, ?v1)) ∧ (?v0 = fun_app$g(of_nat$, ?v1))))
tff(axiom491,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,A__questionmark_v0)
     => ? [A__questionmark_v1: 'Nat$'] :
          ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v1))
          & ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ (∀ ?v3:Nat$ (fun_app$g(?v0, ?v3) < fun_app$g(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1)))) ⇒ ((fun_app$g(?v0, ?v1) < fun_app$g(?v0, ?v2)) = (fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v2))))
tff(axiom492,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$g'(A__questionmark_v0,A__questionmark_v3),'fun_app$g'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1))))
     => ( $less('fun_app$g'(A__questionmark_v0,A__questionmark_v1),'fun_app$g'(A__questionmark_v0,A__questionmark_v2))
      <=> $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$g(?v0, ?v3) < fun_app$g(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v3) + 1)))) ∧ (fun_app$g(of_nat$, ?v1) < fun_app$g(of_nat$, ?v2))) ⇒ (fun_app$g(?v0, ?v1) < fun_app$g(?v0, ?v2)))
tff(axiom493,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$g'(A__questionmark_v0,A__questionmark_v3),'fun_app$g'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v3),1))))
        & $less('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v2)) )
     => $less('fun_app$g'(A__questionmark_v0,A__questionmark_v1),'fun_app$g'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < (fun_app$g(of_nat$, ?v1) + 1)) = ((fun_app$g(of_nat$, ?v0) = 0) ∨ ∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v2) + 1)) ∧ (fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v1)))))
tff(axiom494,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))
    <=> ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
        | ? [A__questionmark_v2: 'Nat$'] :
            ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v2),1) )
            & $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$g(of_nat$, ?v0)) ⇒ ∃ ?v1:Nat$ (fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom495,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
     => ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∀ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < (fun_app$g(of_nat$, ?v0) + 1)) ⇒ fun_app$e(?v1, ?v2)) = (fun_app$e(?v1, fun_app$f(nat$, 0)) ∧ ∀ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v0)) ⇒ fun_app$e(?v1, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))))))
tff(axiom496,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$g'('of_nat$',A__questionmark_v2),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))
         => 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v0))
           => 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1))) ) ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$g(of_nat$, ?v0)) = ∃ ?v1:Nat$ (fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)))
tff(axiom497,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
    <=> ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < (fun_app$g(of_nat$, ?v0) + 1)) ∧ fun_app$e(?v1, ?v2)) = (fun_app$e(?v1, fun_app$f(nat$, 0)) ∨ ∃ ?v2:Nat$ ((fun_app$g(of_nat$, ?v2) < fun_app$g(of_nat$, ?v0)) ∧ fun_app$e(?v1, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))))))
tff(axiom498,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$g'('of_nat$',A__questionmark_v2),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))
          & 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',0))
        | ? [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$g'('of_nat$',A__questionmark_v2),'fun_app$g'('of_nat$',A__questionmark_v0))
            & 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1))) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((0 + 1) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1))) = (((fun_app$g(of_nat$, ?v0) = (0 + 1)) ∧ (fun_app$g(of_nat$, ?v1) = 0)) ∨ ((fun_app$g(of_nat$, ?v0) = 0) ∧ (fun_app$g(of_nat$, ?v1) = (0 + 1)))))
tff(axiom499,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum(0,1) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) )
    <=> ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum(0,1) )
          & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 0 ) )
        | ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
          & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum(0,1) ) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) = (0 + 1)) = (((fun_app$g(of_nat$, ?v0) = (0 + 1)) ∧ (fun_app$g(of_nat$, ?v1) = 0)) ∨ ((fun_app$g(of_nat$, ?v0) = 0) ∧ (fun_app$g(of_nat$, ?v1) = (0 + 1)))))
tff(axiom500,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) = $sum(0,1) )
    <=> ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum(0,1) )
          & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 0 ) )
        | ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
          & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum(0,1) ) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ∧ ∀ ?v2:Nat$ ((fun_app$g(of_nat$, ?v1) = ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) + 1)) ⇒ false)) ⇒ false)
tff(axiom501,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)),1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, ?v0) < ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) + 1))
tff(axiom502,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)),1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, ?v0) < ((fun_app$g(of_nat$, ?v1) + fun_app$g(of_nat$, ?v0)) + 1))
tff(axiom503,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $less('fun_app$g'('of_nat$',A__questionmark_v0),$sum($sum('fun_app$g'('of_nat$',A__questionmark_v1),'fun_app$g'('of_nat$',A__questionmark_v0)),1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) = ∃ ?v2:Nat$ (fun_app$g(of_nat$, ?v1) = ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) + 1)))
tff(axiom504,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> ? [A__questionmark_v2: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, ?v1)) ⇒ ∃ ?v2:Nat$ (fun_app$g(of_nat$, ?v1) = ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v2)) + 1)))
tff(axiom505,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
     => ? [A__questionmark_v2: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v1) = $sum($sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v2)),1) ) ) ).

%% (1 = (0 + 1))
tff(axiom506,axiom,
    1 = $sum(0,1) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) + 1) = (1 + fun_app$g(of_nat$, ?v0)))
tff(axiom507,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum(1,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% (plus$(fun_app$f(nat$, 1)) = suc$)
tff(axiom508,axiom,
    'plus$'('fun_app$f'('nat$',1)) = 'suc$' ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) + 1) = (fun_app$g(of_nat$, ?v0) + 1))
tff(axiom509,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ?v2:Nat_bool_fun$ ?v3:Nat$ ((fun_app$e(?v0, ?v1) ∧ (fun_app$e(?v2, ?v3) ∧ (¬fun_app$e(?v0, fun_app$f(nat$, 0)) ∧ ∀ ?v4:Nat$ (fun_app$e(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v4) + 1))) = fun_app$e(?v2, ?v4))))) ⇒ (fun_app$g(of_nat$, least$a(?v0)) = (fun_app$g(of_nat$, least$a(?v2)) + 1)))
tff(axiom510,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$e'(A__questionmark_v2,A__questionmark_v3)
        & ~ 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0))
        & ! [A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v4),1)))
          <=> 'fun_app$e'(A__questionmark_v2,A__questionmark_v4) ) )
     => ( 'fun_app$g'('of_nat$','least$a'(A__questionmark_v0)) = $sum('fun_app$g'('of_nat$','least$a'(A__questionmark_v2)),1) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$e(?v0, ?v1) ∧ ¬fun_app$e(?v0, fun_app$f(nat$, 0))) ⇒ (fun_app$g(of_nat$, least$a(?v0)) = (fun_app$g(of_nat$, least$a(uuy$(?v0))) + 1)))
tff(axiom511,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
        & ~ 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0)) )
     => ( 'fun_app$g'('of_nat$','least$a'(A__questionmark_v0)) = $sum('fun_app$g'('of_nat$','least$a'('uuy$'(A__questionmark_v0))),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (((0 < fun_app$g(of_nat$, ?v0)) ∧ (fun_app$e(?v1, fun_app$f(nat$, 1)) ∧ ∀ ?v2:Nat$ (((0 < fun_app$g(of_nat$, ?v2)) ∧ fun_app$e(?v1, ?v2)) ⇒ fun_app$e(?v1, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1)))))) ⇒ fun_app$e(?v1, ?v0))
tff(axiom512,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v0))
        & 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',1))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v2))
              & 'fun_app$e'(A__questionmark_v1,A__questionmark_v2) )
           => 'fun_app$e'(A__questionmark_v1,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1))) ) )
     => 'fun_app$e'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ((1 < fun_app$g(of_nat$, ?v0)) ⇒ (1 < fun_app$g(of_nat$, ?v0)))
tff(axiom513,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(1,'fun_app$g'('of_nat$',A__questionmark_v0))
     => $less(1,'fun_app$g'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ (fun_app$(of_nat$a, ?v0) = fun_app$(of_nat_aux$(uuz$, ?v0), zero$c))
tff(axiom514,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$'('of_nat$a',A__questionmark_v0) = 'fun_app$'('of_nat_aux$'('uuz$',A__questionmark_v0),'zero$c') ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, ?v0) = fun_app$a(of_nat_aux$a(uva$, ?v0), 0))
tff(axiom515,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$a'('of_nat_aux$a'('uva$',A__questionmark_v0),0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom516,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Bool ?v1:Nat$ ?v2:Nat$ (fun_app$g(of_nat$, (if ?v0 ?v1 else ?v2)) = (if ?v0 fun_app$g(of_nat$, ?v1) else fun_app$g(of_nat$, ?v2)))
tff(axiom517,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 'fun_app$g'('of_nat$',A__questionmark_v2) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$g'('of_nat$',A__questionmark_v2) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$g'('of_nat$',A__questionmark_v2) = 'fun_app$g'('of_nat$',A__questionmark_v2) ) ) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)))
tff(axiom518,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ((¬fun_app$e(?v0, fun_app$f(nat$, 0)) ∧ ∃ ?v1:Nat$ fun_app$e(?v0, ?v1)) ⇒ ∃ ?v1:Nat$ (¬fun_app$e(?v0, ?v1) ∧ fun_app$e(?v0, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1)))))
tff(axiom519,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ( ~ 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0))
        & ? [A__questionmark_v1: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v1) )
     => ? [A__questionmark_v1: 'Nat$'] :
          ( ~ 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
          & 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1))) ) ) ).

%% ∀ ?v0:Nat$ ((((fun_app$g(of_nat$, ?v0) = 0) ⇒ false) ∧ ∀ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) = (fun_app$g(of_nat$, ?v1) + 1)) ⇒ false)) ⇒ false)
tff(axiom520,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = $sum('fun_app$g'('of_nat$',A__questionmark_v1),1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, fun_app$(triangle$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1)))) = (fun_app$g(of_nat$, fun_app$(triangle$, ?v0)) + (fun_app$g(of_nat$, ?v0) + 1)))
tff(axiom521,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$'('triangle$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)))) = $sum('fun_app$g'('of_nat$','fun_app$'('triangle$',A__questionmark_v0)),$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)) ) ).

%% ∀ ?v0:Int (((0 + 1) < fun_app$g(of_nat$, fun_app$f(nat$, ?v0))) = (1 < ?v0))
tff(axiom522,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($sum(0,1),'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)))
    <=> $less(1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int (((?v0 < 0) ∧ ∀ ?v1:Nat$ (((?v0 = -fun_app$g(of_nat$, ?v1)) ∧ (0 < fun_app$g(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom523,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $less(A__questionmark_v0,0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$',A__questionmark_v1)) )
              & $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int (--?v0 = ?v0)
tff(axiom524,axiom,
    ! [A__questionmark_v0: $int] : ( $uminus($uminus(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (--?v0 = ?v0)
tff(axiom525,axiom,
    ! [A__questionmark_v0: $int] : ( $uminus($uminus(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 = -?v1) = (?v0 = ?v1))
tff(axiom526,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $uminus(A__questionmark_v0) = $uminus(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ((-?v0 = ?v0) = (?v0 = 0))
tff(axiom527,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Int ((?v0 = -?v0) = (?v0 = 0))
tff(axiom528,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v0) )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Int ((-?v0 = 0) = (?v0 = 0))
tff(axiom529,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $uminus(A__questionmark_v0) = 0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Int ((0 = -?v0) = (0 = ?v0))
tff(axiom530,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = $uminus(A__questionmark_v0) )
    <=> ( 0 = A__questionmark_v0 ) ) ).

%% (0 = 0)
tff(axiom531,axiom,
    0 = 0 ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 < -?v1) = (?v1 < ?v0))
tff(axiom532,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int (-(?v0 + ?v1) = (-?v0 + -?v1))
tff(axiom533,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $uminus($sum(A__questionmark_v0,A__questionmark_v1)) = $sum($uminus(A__questionmark_v0),$uminus(A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 + (?v0 + ?v1)) = ?v1)
tff(axiom534,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $sum($uminus(A__questionmark_v0),$sum(A__questionmark_v0,A__questionmark_v1)) = A__questionmark_v1 ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 + (-?v0 + ?v1)) = ?v1)
tff(axiom535,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $sum(A__questionmark_v0,$sum($uminus(A__questionmark_v0),A__questionmark_v1)) = A__questionmark_v1 ) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v0))
tff(axiom536,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ).

%% (fun_app$g(of_nat$, fun_app$(triangle$, fun_app$f(nat$, 0))) = 0)
tff(axiom537,axiom,
    'fun_app$g'('of_nat$','fun_app$'('triangle$','fun_app$f'('nat$',0))) = 0 ).

%% ∀ ?v0:Int ((-?v0 < 0) = (0 < ?v0))
tff(axiom538,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($uminus(A__questionmark_v0),0)
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((0 < -?v0) = (?v0 < 0))
tff(axiom539,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((-?v0 < ?v0) = (0 < ?v0))
tff(axiom540,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((?v0 < -?v0) = (?v0 < 0))
tff(axiom541,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((-?v0 + ?v0) = 0)
tff(axiom542,axiom,
    ! [A__questionmark_v0: $int] : ( $sum($uminus(A__questionmark_v0),A__questionmark_v0) = 0 ) ).

%% ∀ ?v0:Int ((?v0 + -?v0) = 0)
tff(axiom543,axiom,
    ! [A__questionmark_v0: $int] : ( $sum(A__questionmark_v0,$uminus(A__questionmark_v0)) = 0 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((-fun_app$g(of_nat$, ?v0) = fun_app$g(of_nat$, ?v1)) = ((fun_app$g(of_nat$, ?v0) = 0) ∧ (fun_app$g(of_nat$, ?v1) = 0)))
tff(axiom544,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $uminus('fun_app$g'('of_nat$',A__questionmark_v0)) = 'fun_app$g'('of_nat$',A__questionmark_v1) )
    <=> ( ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 )
        & ( 'fun_app$g'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% (fun_app$a(dbl_inc$, -1) = -1)
tff(axiom545,axiom,
    'fun_app$a'('dbl_inc$',$uminus(1)) = $uminus(1) ).

%% ((1 + -1) = 0)
tff(axiom546,axiom,
    $sum(1,$uminus(1)) = 0 ).

%% ((-1 + 1) = 0)
tff(axiom547,axiom,
    $sum($uminus(1),1) = 0 ).

%% (fun_app$g(of_nat$, fun_app$f(nat$, 1)) = (0 + 1))
tff(axiom548,axiom,
    'fun_app$g'('of_nat$','fun_app$f'('nat$',1)) = $sum(0,1) ).

%% ∀ ?v0:Int ?v1:Int ((fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) < fun_app$g(of_nat$, fun_app$f(nat$, ?v1))) = ((0 < ?v1) ∧ (?v0 < ?v1)))
tff(axiom549,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less('fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)),'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v1)))
    <=> ( $less(0,A__questionmark_v1)
        & $less(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (-fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) < fun_app$g(of_nat$, ?v1))
tff(axiom550,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $less($uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)))),'fun_app$g'('of_nat$',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, -fun_app$g(of_nat$, ?v0))) = 0)
tff(axiom551,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$uminus('fun_app$g'('of_nat$',A__questionmark_v0)))) = 0 ) ).

%% ∀ ?v0:Int ((0 < fun_app$g(of_nat$, fun_app$f(nat$, ?v0))) = (0 < ?v0))
tff(axiom552,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)))
    <=> $less(0,A__questionmark_v0) ) ).

%% (0 = fun_app$g(of_nat$, fun_app$f(nat$, 0)))
tff(axiom553,axiom,
    0 = 'fun_app$g'('of_nat$','fun_app$f'('nat$',0)) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) = 0) = (?v1 = -?v0))
tff(axiom554,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = 0 )
    <=> ( A__questionmark_v1 = $uminus(A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ((-?v0 + ?v0) = 0)
tff(axiom555,axiom,
    ! [A__questionmark_v0: $int] : ( $sum($uminus(A__questionmark_v0),A__questionmark_v0) = 0 ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) = 0) ⇒ (-?v0 = ?v1))
tff(axiom556,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $sum(A__questionmark_v0,A__questionmark_v1) = 0 )
     => ( $uminus(A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = -?v1) = ((?v0 + ?v1) = 0))
tff(axiom557,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v1) )
    <=> ( $sum(A__questionmark_v0,A__questionmark_v1) = 0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 = ?v1) = ((?v0 + ?v1) = 0))
tff(axiom558,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v1 )
    <=> ( $sum(A__questionmark_v0,A__questionmark_v1) = 0 ) ) ).

%% ¬(0 = -1)
tff(axiom559,axiom,
    0 != $uminus(1) ).

%% (1 = fun_app$g(of_nat$, fun_app$f(nat$, 1)))
tff(axiom560,axiom,
    1 = 'fun_app$g'('of_nat$','fun_app$f'('nat$',1)) ).

%% (-1 < 1)
tff(axiom561,axiom,
    $less($uminus(1),1) ).

%% ¬(1 < -1)
tff(axiom562,axiom,
    ~ $less(1,$uminus(1)) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$g(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ ((?v0 = -fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1)))) ⇒ false)) ⇒ false)
tff(axiom563,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)))) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int_bool_fun$ ?v1:Int ((∀ ?v2:Nat$ fun_app$b(?v0, fun_app$g(of_nat$, ?v2)) ∧ ∀ ?v2:Nat$ fun_app$b(?v0, -fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v2) + 1))))) ⇒ fun_app$b(?v0, ?v1))
tff(axiom564,axiom,
    ! [A__questionmark_v0: 'Int_bool_fun$',A__questionmark_v1: $int] :
      ( ( ! [A__questionmark_v2: 'Nat$'] : 'fun_app$b'(A__questionmark_v0,'fun_app$g'('of_nat$',A__questionmark_v2))
        & ! [A__questionmark_v2: 'Nat$'] : 'fun_app$b'(A__questionmark_v0,$uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v2),1))))) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = ?v1) ⇒ (-?v0 = -?v1))
tff(axiom565,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => ( $uminus(A__questionmark_v0) = $uminus(A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = -?v1) = (?v1 = -?v0))
tff(axiom566,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v1) )
    <=> ( A__questionmark_v1 = $uminus(A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 = ?v1) = (-?v1 = ?v0))
tff(axiom567,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v1 )
    <=> ( $uminus(A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% (0 = 0)
tff(axiom568,axiom,
    0 = 0 ).

%% ¬(1 = -1)
tff(axiom569,axiom,
    1 != $uminus(1) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < -?v1) = (?v1 < -?v0))
tff(axiom570,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 < ?v1) = (-?v1 < ?v0))
tff(axiom571,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $less($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ (-?v1 < -?v0))
tff(axiom572,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int (-(?v0 + ?v1) = (-?v1 + -?v0))
tff(axiom573,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $uminus($sum(A__questionmark_v0,A__questionmark_v1)) = $sum($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int (-(?v0 + ?v1) = (-?v1 + -?v0))
tff(axiom574,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( $uminus($sum(A__questionmark_v0,A__questionmark_v1)) = $sum($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 = (?v1 + ?v2)) ⇒ (-?v0 = (-?v1 + -?v2)))
tff(axiom575,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( A__questionmark_v0 = $sum(A__questionmark_v1,A__questionmark_v2) )
     => ( $uminus(A__questionmark_v0) = $sum($uminus(A__questionmark_v1),$uminus(A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$g(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ ((?v0 = -fun_app$g(of_nat$, ?v1)) ⇒ false)) ⇒ false)
tff(axiom576,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ¬(fun_app$g(of_nat$, ?v0) < -fun_app$g(of_nat$, ?v1))
tff(axiom577,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ~ $less('fun_app$g'('of_nat$',A__questionmark_v0),$uminus('fun_app$g'('of_nat$',A__questionmark_v1))) ).

%% ∀ ?v0:Int ?v1:Int ((0 < ?v0) ⇒ ((fun_app$g(of_nat$, fun_app$f(nat$, ?v1)) < fun_app$g(of_nat$, fun_app$f(nat$, ?v0))) = (?v1 < ?v0)))
tff(axiom578,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(0,A__questionmark_v0)
     => ( $less('fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v1)),'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)))
      <=> $less(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Int ((fun_app$g(of_nat$, ?v0) < fun_app$g(of_nat$, fun_app$f(nat$, ?v1))) = (fun_app$g(of_nat$, ?v0) < ?v1))
tff(axiom579,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $int] :
      ( $less('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v1)))
    <=> $less('fun_app$g'('of_nat$',A__questionmark_v0),A__questionmark_v1) ) ).

%% (-1 < 0)
tff(axiom580,axiom,
    $less($uminus(1),0) ).

%% ¬(0 < -1)
tff(axiom581,axiom,
    ~ $less(0,$uminus(1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))) = (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))
tff(axiom582,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) = $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$g(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ (((0 < fun_app$g(of_nat$, ?v1)) ∧ (?v0 = -fun_app$g(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom583,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( $less(0,'fun_app$g'('of_nat$',A__questionmark_v1))
              & ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$',A__questionmark_v1)) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)) = fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + fun_app$g(of_nat$, ?v1)))))
tff(axiom584,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) = 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)))) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Int (fun_app$e(?v0, fun_app$f(nat$, ?v1)) = (∀ ?v2:Nat$ ((?v1 = fun_app$g(of_nat$, ?v2)) ⇒ fun_app$e(?v0, ?v2)) ∧ ((?v1 < 0) ⇒ fun_app$e(?v0, fun_app$f(nat$, 0)))))
tff(axiom585,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: $int] :
      ( 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',A__questionmark_v1))
    <=> ( ! [A__questionmark_v2: 'Nat$'] :
            ( ( A__questionmark_v1 = 'fun_app$g'('of_nat$',A__questionmark_v2) )
           => 'fun_app$e'(A__questionmark_v0,A__questionmark_v2) )
        & ( $less(A__questionmark_v1,0)
         => 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',0)) ) ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) + 1) = fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))))
tff(axiom586,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$g'('of_nat$',A__questionmark_v0),1) = 'fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1))) ) ).

%% ∀ ?v0:Int ((((?v0 = 0) ⇒ false) ∧ (∀ ?v1:Nat$ (((?v0 = fun_app$g(of_nat$, ?v1)) ∧ (0 < fun_app$g(of_nat$, ?v1))) ⇒ false) ∧ ∀ ?v1:Nat$ (((?v0 = -fun_app$g(of_nat$, ?v1)) ∧ (0 < fun_app$g(of_nat$, ?v1))) ⇒ false))) ⇒ false)
tff(axiom587,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ( ( A__questionmark_v0 = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
              & $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$',A__questionmark_v1)) )
              & $less(0,'fun_app$g'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ((?v0 < 0) ⇒ ∃ ?v1:Nat$ (?v0 = -fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v1) + 1)))))
tff(axiom588,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,0)
     => ? [A__questionmark_v1: 'Nat$'] : ( A__questionmark_v0 = $uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v1),1)))) ) ) ).

%% ∀ ?v0:Nat$ (-fun_app$g(of_nat$, fun_app$f(nat$, (fun_app$g(of_nat$, ?v0) + 1))) < 0)
tff(axiom589,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less($uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$sum('fun_app$g'('of_nat$',A__questionmark_v0),1)))),0) ).

%% (fun_app$a(dbl_dec$, 0) = -1)
tff(axiom590,axiom,
    'fun_app$a'('dbl_dec$',0) = $uminus(1) ).

%% (fun_app$a(dbl_dec$, 1) = 1)
tff(axiom591,axiom,
    'fun_app$a'('dbl_dec$',1) = 1 ).

%% ∀ ?v0:Int (fun_app$a(of_int$, ?v0) = (if (?v0 < 0) -fun_app$g(of_nat$, fun_app$f(nat$, -?v0)) else fun_app$g(of_nat$, fun_app$f(nat$, ?v0))))
tff(axiom592,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $less(A__questionmark_v0,0)
       => ( 'fun_app$a'('of_int$',A__questionmark_v0) = $uminus('fun_app$g'('of_nat$','fun_app$f'('nat$',$uminus(A__questionmark_v0)))) ) )
      & ( ~ $less(A__questionmark_v0,0)
       => ( 'fun_app$a'('of_int$',A__questionmark_v0) = 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) ) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 ≤ ?v0) ⇒ ((fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) < fun_app$g(of_nat$, ?v1)) = (?v0 < fun_app$g(of_nat$, ?v1))))
tff(axiom593,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0,A__questionmark_v0)
     => ( $less('fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)),'fun_app$g'('of_nat$',A__questionmark_v1))
      <=> $less(A__questionmark_v0,'fun_app$g'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Int (?v0 ≤ ?v0)
tff(axiom594,axiom,
    ! [A__questionmark_v0: $int] : $lesseq(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Int (?v0 ≤ ?v0)
tff(axiom595,axiom,
    ! [A__questionmark_v0: $int] : $lesseq(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less_eq$, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v2), ?v1)) = fun_app$e(fun_app$u(less_eq$, ?v0), ?v2))
tff(axiom596,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v2),A__questionmark_v1))
    <=> 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) ≤ (?v2 + ?v1)) = (?v0 ≤ ?v2))
tff(axiom597,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v2,A__questionmark_v1))
    <=> $lesseq(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$e(fun_app$u(less_eq$, fun_app$(plus$(?v0), ?v1)), fun_app$(plus$(?v0), ?v2)) = fun_app$e(fun_app$u(less_eq$, ?v1), ?v2))
tff(axiom598,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v2))
    <=> 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 + ?v1) ≤ (?v0 + ?v2)) = (?v1 ≤ ?v2))
tff(axiom599,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq($sum(A__questionmark_v0,A__questionmark_v1),$sum(A__questionmark_v0,A__questionmark_v2))
    <=> $lesseq(A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 ≤ -?v1) = (?v1 ≤ ?v0))
tff(axiom600,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$g(of_nat$, ?v0) ≤ fun_app$g(of_nat$, ?v1)) = (fun_app$g(of_nat$, ?v0) ≤ fun_app$g(of_nat$, ?v1)))
tff(axiom601,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1))
    <=> $lesseq('fun_app$g'('of_nat$',A__questionmark_v0),'fun_app$g'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less_eq$, fun_app$(plus$(?v0), ?v1)), ?v0) = fun_app$e(fun_app$u(less_eq$, ?v1), zero$c))
tff(axiom602,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0)
    <=> 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v1),'zero$c') ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) ≤ ?v0) = (?v1 ≤ 0))
tff(axiom603,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v0)
    <=> $lesseq(A__questionmark_v1,0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less_eq$, fun_app$(plus$(?v0), ?v1)), ?v1) = fun_app$e(fun_app$u(less_eq$, ?v0), zero$c))
tff(axiom604,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1)
    <=> 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v0),'zero$c') ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 + ?v1) ≤ ?v1) = (?v0 ≤ 0))
tff(axiom605,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v1)
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less_eq$, ?v0), fun_app$(plus$(?v0), ?v1)) = fun_app$e(fun_app$u(less_eq$, zero$c), ?v1))
tff(axiom606,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1))
    <=> 'fun_app$e'('fun_app$u'('less_eq$','zero$c'),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ (?v0 + ?v1)) = (0 ≤ ?v1))
tff(axiom607,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,$sum(A__questionmark_v0,A__questionmark_v1))
    <=> $lesseq(0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$e(fun_app$u(less_eq$, ?v0), fun_app$(plus$(?v1), ?v0)) = fun_app$e(fun_app$u(less_eq$, zero$c), ?v1))
tff(axiom608,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v0),'fun_app$'('plus$'(A__questionmark_v1),A__questionmark_v0))
    <=> 'fun_app$e'('fun_app$u'('less_eq$','zero$c'),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ (?v1 + ?v0)) = (0 ≤ ?v1))
tff(axiom609,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,$sum(A__questionmark_v1,A__questionmark_v0))
    <=> $lesseq(0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int (((?v0 + ?v0) ≤ 0) = (?v0 ≤ 0))
tff(axiom610,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq($sum(A__questionmark_v0,A__questionmark_v0),0)
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((0 ≤ (?v0 + ?v0)) = (0 ≤ ?v0))
tff(axiom611,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,$sum(A__questionmark_v0,A__questionmark_v0))
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((0 ≤ -?v0) = (?v0 ≤ 0))
tff(axiom612,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((-?v0 ≤ 0) = (0 ≤ ?v0))
tff(axiom613,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq($uminus(A__questionmark_v0),0)
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((?v0 ≤ -?v0) = (?v0 ≤ 0))
tff(axiom614,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((-?v0 ≤ ?v0) = (0 ≤ ?v0))
tff(axiom615,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% (fun_app$a(of_int$, 0) = 0)
tff(axiom616,axiom,
    'fun_app$a'('of_int$',0) = 0 ).

%% ∀ ?v0:Int ((0 = fun_app$a(of_int$, ?v0)) = (?v0 = 0))
tff(axiom617,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = 'fun_app$a'('of_int$',A__questionmark_v0) )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) = 0) = (?v0 = 0))
tff(axiom618,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 'fun_app$a'('of_int$',A__questionmark_v0) = 0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((fun_app$a(of_int$, ?v0) ≤ fun_app$a(of_int$, ?v1)) = (?v0 ≤ ?v1))
tff(axiom619,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq('fun_app$a'('of_int$',A__questionmark_v0),'fun_app$a'('of_int$',A__questionmark_v1))
    <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((fun_app$a(of_int$, ?v0) < fun_app$a(of_int$, ?v1)) = (?v0 < ?v1))
tff(axiom620,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less('fun_app$a'('of_int$',A__questionmark_v0),'fun_app$a'('of_int$',A__questionmark_v1))
    <=> $less(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) = 1) = (?v0 = 1))
tff(axiom621,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 'fun_app$a'('of_int$',A__questionmark_v0) = 1 )
    <=> ( A__questionmark_v0 = 1 ) ) ).

%% (fun_app$a(of_int$, 1) = 1)
tff(axiom622,axiom,
    'fun_app$a'('of_int$',1) = 1 ).

%% ∀ ?v0:Int ?v1:Int (fun_app$a(of_int$, (?v0 + ?v1)) = (fun_app$a(of_int$, ?v0) + fun_app$a(of_int$, ?v1)))
tff(axiom623,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( 'fun_app$a'('of_int$',$sum(A__questionmark_v0,A__questionmark_v1)) = $sum('fun_app$a'('of_int$',A__questionmark_v0),'fun_app$a'('of_int$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int (fun_app$a(of_int$, -?v0) = -fun_app$a(of_int$, ?v0))
tff(axiom624,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$a'('of_int$',$uminus(A__questionmark_v0)) = $uminus('fun_app$a'('of_int$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ (fun_app$a(of_int$, fun_app$g(of_nat$, ?v0)) = fun_app$g(of_nat$, ?v0))
tff(axiom625,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$a'('of_int$','fun_app$g'('of_nat$',A__questionmark_v0)) = 'fun_app$g'('of_nat$',A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (-fun_app$g(of_nat$, ?v0) ≤ fun_app$g(of_nat$, ?v1))
tff(axiom626,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $lesseq($uminus('fun_app$g'('of_nat$',A__questionmark_v0)),'fun_app$g'('of_nat$',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ((fun_app$g(of_nat$, ?v0) ≤ 0) = (fun_app$g(of_nat$, ?v0) = 0))
tff(axiom627,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$g'('of_nat$',A__questionmark_v0),0)
    <=> ( 'fun_app$g'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Int ((?v0 ≤ 0) ⇒ (fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = 0))
tff(axiom628,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(A__questionmark_v0,0)
     => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 0 ) ) ).

%% ∀ ?v0:Int ((fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = 0) = (?v0 ≤ 0))
tff(axiom629,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 0 )
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < (?v1 + 1)) = (?v0 ≤ ?v1))
tff(axiom630,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,$sum(A__questionmark_v1,1))
    <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int (fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = (if (0 ≤ ?v0) ?v0 else 0))
tff(axiom631,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = A__questionmark_v0 ) )
      & ( ~ $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 0 ) ) ) ).

%% ∀ ?v0:Int ((0 ≤ fun_app$a(of_int$, ?v0)) = (0 ≤ ?v0))
tff(axiom632,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,'fun_app$a'('of_int$',A__questionmark_v0))
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) ≤ 0) = (?v0 ≤ 0))
tff(axiom633,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq('fun_app$a'('of_int$',A__questionmark_v0),0)
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((0 < fun_app$a(of_int$, ?v0)) = (0 < ?v0))
tff(axiom634,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,'fun_app$a'('of_int$',A__questionmark_v0))
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) < 0) = (?v0 < 0))
tff(axiom635,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less('fun_app$a'('of_int$',A__questionmark_v0),0)
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Int ((1 ≤ fun_app$a(of_int$, ?v0)) = (1 ≤ ?v0))
tff(axiom636,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(1,'fun_app$a'('of_int$',A__questionmark_v0))
    <=> $lesseq(1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) ≤ 1) = (?v0 ≤ 1))
tff(axiom637,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq('fun_app$a'('of_int$',A__questionmark_v0),1)
    <=> $lesseq(A__questionmark_v0,1) ) ).

%% ∀ ?v0:Int ((1 < fun_app$a(of_int$, ?v0)) = (1 < ?v0))
tff(axiom638,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(1,'fun_app$a'('of_int$',A__questionmark_v0))
    <=> $less(1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((fun_app$a(of_int$, ?v0) < 1) = (?v0 < 1))
tff(axiom639,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less('fun_app$a'('of_int$',A__questionmark_v0),1)
    <=> $less(A__questionmark_v0,1) ) ).

%% ∀ ?v0:Int ((0 ≤ ?v0) ⇒ (fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = fun_app$a(of_int$, ?v0)))
tff(axiom640,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,A__questionmark_v0)
     => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 'fun_app$a'('of_int$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ -?v1) = (?v1 ≤ -?v0))
tff(axiom641,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 ≤ ?v1) = (-?v1 ≤ ?v0))
tff(axiom642,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $lesseq($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (-?v1 ≤ -?v0))
tff(axiom643,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ¬(1 ≤ -1)
tff(axiom644,axiom,
    ~ $lesseq(1,$uminus(1)) ).

%% (-1 ≤ 1)
tff(axiom645,axiom,
    $lesseq($uminus(1),1) ).

%% ∀ ?v0:Int ((0 ≤ ?v0) ⇒ ∃ ?v1:Nat$ (?v0 = fun_app$g(of_nat$, ?v1)))
tff(axiom646,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,A__questionmark_v0)
     => ? [A__questionmark_v1: 'Nat$'] : ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int (((0 ≤ ?v0) ∧ ∀ ?v1:Nat$ ((?v0 = fun_app$g(of_nat$, ?v1)) ⇒ false)) ⇒ false)
tff(axiom647,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('of_nat$',A__questionmark_v1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((0 ≤ ?v0) ∧ (0 ≤ ?v1)) ⇒ ((fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = fun_app$g(of_nat$, fun_app$f(nat$, ?v1))) = (?v0 = ?v1)))
tff(axiom648,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
        & $lesseq(0,A__questionmark_v1) )
     => ( ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v1)) )
      <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∀ ?v1:Nat$ fun_app$e(?v0, ?v1) = ∀ ?v1:Int ((0 ≤ ?v1) ⇒ fun_app$e(?v0, fun_app$f(nat$, ?v1))))
tff(axiom649,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v1: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v1: $int] :
          ( $lesseq(0,A__questionmark_v1)
         => 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∃ ?v1:Nat$ fun_app$e(?v0, ?v1) = ∃ ?v1:Int ((0 ≤ ?v1) ∧ fun_app$e(?v0, fun_app$f(nat$, ?v1))))
tff(axiom650,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v1: 'Nat$'] : 'fun_app$e'(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v1: $int] :
          ( $lesseq(0,A__questionmark_v1)
          & 'fun_app$e'(A__questionmark_v0,'fun_app$f'('nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_bool_fun$ (((?v0 ≤ ?v1) ∧ (fun_app$b(?v2, ?v0) ∧ ∀ ?v3:Int (((?v0 ≤ ?v3) ∧ fun_app$b(?v2, ?v3)) ⇒ fun_app$b(?v2, (?v3 + 1))))) ⇒ fun_app$b(?v2, ?v1))
tff(axiom651,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_bool_fun$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$b'(A__questionmark_v2,A__questionmark_v0)
        & ! [A__questionmark_v3: $int] :
            ( ( $lesseq(A__questionmark_v0,A__questionmark_v3)
              & 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) )
           => 'fun_app$b'(A__questionmark_v2,$sum(A__questionmark_v3,1)) ) )
     => 'fun_app$b'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = ∃ ?v2:Nat$ (?v1 = (?v0 + fun_app$g(of_nat$, ?v2))))
tff(axiom652,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v2: 'Nat$'] : ( A__questionmark_v1 = $sum(A__questionmark_v0,'fun_app$g'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$e(fun_app$u(less_eq$, ?v0), zero$c) ∧ fun_app$e(fun_app$u(less_eq$, ?v1), ?v2)) ⇒ fun_app$e(fun_app$u(less_eq$, fun_app$(plus$(?v0), ?v1)), ?v2))
tff(axiom653,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v0),'zero$c')
        & 'fun_app$e'('fun_app$u'('less_eq$',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$e'('fun_app$u'('less_eq$','fun_app$'('plus$'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ 0) ∧ (?v1 ≤ ?v2)) ⇒ ((?v0 + ?v1) ≤ ?v2))
tff(axiom654,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,0)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq($sum(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$g(of_nat$, ?v0))
tff(axiom655,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$g'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ (fun_app$f(nat$, fun_app$g(of_nat$, ?v0)) = ?v0)
tff(axiom656,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$f'('nat$','fun_app$g'('of_nat$',A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$g(of_nat$, fun_app$f(nat$, ?v0)) = (if (0 ≤ ?v0) ?v0 else 0))
tff(axiom657,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = A__questionmark_v0 ) )
      & ( ~ $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$g'('of_nat$','fun_app$f'('nat$',A__questionmark_v0)) = 0 ) ) ) ).

%% ∀ b:tlbool ((b = tltrue) ∨ (b = tlfalse))
tff(formula_659,axiom,
    ! [B: tlbool] :
      ( ( B = tltrue )
      | ( B = tlfalse ) ) ).

%% ¬(tltrue = tlfalse)
tff(formula_660,axiom,
    tltrue != tlfalse ).

%------------------------------------------------------------------------------

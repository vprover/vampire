%------------------------------------------------------------------------------
% File     : ITP001_1 : TPTP v9.0.0. Released v8.1.0.
% Domain   : Interactive Theorem Proving
% Problem  : SMT-LIB Gauss_Jordan Rref 00399_018572
% Version  : [Des21] axioms.
% English  :

% Refs     : [Des21] Desharnais (2021), Email to Geoff Sutcliffe
% Source   : [Des21]
% Names    : Gauss_Jordan-0017_Rref-prob_00399_018572 [Des21]

% Status   : Theorem
% Rating   : 0.38 v8.1.0
% Syntax   : Number of formulae    :  777 ( 154 unt; 159 typ;   0 def)
%            Number of atoms       : 1521 ( 422 equ)
%            Maximal formula atoms :   10 (   2 avg)
%            Number of connectives : 1034 ( 131   ~;  26   |; 256   &)
%                                         ( 232 <=>; 389  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   14 (   4 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number arithmetic     : 1965 ( 710 atm; 237 fun; 731 num; 287 var)
%            Number of types       :   43 (  40 usr;   2 ari)
%            Number of type conns  :  141 (  89   >;  52   *;   0   +;   0  <<)
%            Number of predicates  :   24 (  19 usr;   2 prp; 0-3 aty)
%            Number of functors    :  106 ( 100 usr;  34 con; 0-2 aty)
%            Number of variables   : 1129 (1092   !;  37   ?;1129   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Translated from SMT format using smttotptp 0.9.10. See
%            https://bitbucket.org/peba123/smttotptp/src/master/
%          : SMT-LIB AUFLIRA logic
%------------------------------------------------------------------------------
%% Types:
tff('Int_bool_fun$',type,
    'Int_bool_fun$': $tType ).

tff('Rows_rows_bool_fun_fun$',type,
    'Rows_rows_bool_fun_fun$': $tType ).

tff('Nat_nat_bool_fun_fun$',type,
    'Nat_nat_bool_fun_fun$': $tType ).

tff('Rows_rows_vec$',type,
    'Rows_rows_vec$': $tType ).

tff('Real_cols_vec_rows_vec$',type,
    'Real_cols_vec_rows_vec$': $tType ).

tff('Rows_rows_vec_rows_vec$',type,
    'Rows_rows_vec_rows_vec$': $tType ).

tff('Rows$',type,
    'Rows$': $tType ).

tff('Int_rows_vec$',type,
    'Int_rows_vec$': $tType ).

tff('Rows_a_cols_vec_fun$',type,
    'Rows_a_cols_vec_fun$': $tType ).

tff('Int_rows_vec_rows_vec$',type,
    'Int_rows_vec_rows_vec$': $tType ).

tff('Cols_cols_vec_rows_vec$',type,
    'Cols_cols_vec_rows_vec$': $tType ).

tff('Nat_nat_fun$',type,
    'Nat_nat_fun$': $tType ).

tff('Nat$',type,
    'Nat$': $tType ).

tff('Real_rows_vec$',type,
    'Real_rows_vec$': $tType ).

tff('Rows_cols_vec_rows_vec$',type,
    'Rows_cols_vec_rows_vec$': $tType ).

tff('A_rows_vec$',type,
    'A_rows_vec$': $tType ).

tff('Cols_rows_vec$',type,
    'Cols_rows_vec$': $tType ).

tff(tlbool,type,
    tlbool: $tType ).

tff('Real_rows_vec_cols_vec$',type,
    'Real_rows_vec_cols_vec$': $tType ).

tff('Rows_bool_fun$',type,
    'Rows_bool_fun$': $tType ).

tff('Int_cols_vec$',type,
    'Int_cols_vec$': $tType ).

tff('A_cols_vec_rows_vec$',type,
    'A_cols_vec_rows_vec$': $tType ).

tff('Real_cols_vec$',type,
    'Real_cols_vec$': $tType ).

tff('Rows_cols_vec$',type,
    'Rows_cols_vec$': $tType ).

tff('Nat_real_fun$',type,
    'Nat_real_fun$': $tType ).

tff('A_cols_vec$',type,
    'A_cols_vec$': $tType ).

tff('A$',type,
    'A$': $tType ).

tff('Real_rows_vec_rows_vec$',type,
    'Real_rows_vec_rows_vec$': $tType ).

tff('Cols_rows_vec_rows_vec$',type,
    'Cols_rows_vec_rows_vec$': $tType ).

tff('A_a_fun$',type,
    'A_a_fun$': $tType ).

tff('Cols$',type,
    'Cols$': $tType ).

tff('Nat_rows_fun$',type,
    'Nat_rows_fun$': $tType ).

tff('A_rows_vec_rows_vec$',type,
    'A_rows_vec_rows_vec$': $tType ).

tff('Nat_bool_fun$',type,
    'Nat_bool_fun$': $tType ).

tff('Real_bool_fun$',type,
    'Real_bool_fun$': $tType ).

tff('Cols_a_fun$',type,
    'Cols_a_fun$': $tType ).

tff('Real_set$',type,
    'Real_set$': $tType ).

tff('Nat_int_fun$',type,
    'Nat_int_fun$': $tType ).

tff('Cols_cols_vec$',type,
    'Cols_cols_vec$': $tType ).

tff('Int_cols_vec_rows_vec$',type,
    'Int_cols_vec_rows_vec$': $tType ).

%% Declarations:
tff('column$d',type,
    'column$d': ( 'Rows$' * 'Cols_rows_vec_rows_vec$' ) > 'Cols_rows_vec$' ).

tff('one$e',type,
    'one$e': 'Nat$' ).

tff('one$c',type,
    'one$c': 'Rows$' ).

tff('reduced_row_echelon_form$f',type,
    'reduced_row_echelon_form$f': 'Real_cols_vec_rows_vec$' > $o ).

tff('column$b',type,
    'column$b': ( 'Rows$' * 'Int_rows_vec_rows_vec$' ) > 'Int_rows_vec$' ).

tff('zero$k',type,
    'zero$k': 'Nat$' ).

tff('vec_nth$c',type,
    'vec_nth$c': ( 'Real_rows_vec_rows_vec$' * 'Rows$' ) > 'Real_rows_vec$' ).

tff('column$h',type,
    'column$h': ( 'Cols$' * 'Rows_cols_vec_rows_vec$' ) > 'Rows_rows_vec$' ).

tff('column$',type,
    'column$': ( 'Cols$' * 'A_cols_vec_rows_vec$' ) > 'A_rows_vec$' ).

tff('fun_app$d',type,
    'fun_app$d': ( 'Rows_rows_bool_fun_fun$' * 'Rows$' ) > 'Rows_bool_fun$' ).

tff('axis$',type,
    'axis$': ( 'Cols$' * 'A$' ) > 'A_cols_vec$' ).

tff('vec_nth$b',type,
    'vec_nth$b': ( 'Real_rows_vec$' * 'Rows$' ) > $real ).

tff('vec_nth$s',type,
    'vec_nth$s': ( 'Cols_cols_vec_rows_vec$' * 'Rows$' ) > 'Cols_cols_vec$' ).

tff('reduced_row_echelon_form$g',type,
    'reduced_row_echelon_form$g': 'Int_cols_vec_rows_vec$' > $o ).

tff('one$a',type,
    'one$a': 'A$' ).

tff('vec_nth$e',type,
    'vec_nth$e': ( 'Int_rows_vec_rows_vec$' * 'Rows$' ) > 'Int_rows_vec$' ).

tff('vec_nth$',type,
    'vec_nth$': 'A_cols_vec$' > 'Cols_a_fun$' ).

tff('is_zero_row_upt_k$',type,
    'is_zero_row_upt_k$': ( 'Rows$' * 'Nat$' * 'A_cols_vec_rows_vec$' ) > $o ).

tff('vec_nth$n',type,
    'vec_nth$n': ( 'Int_cols_vec$' * 'Cols$' ) > $int ).

tff('fun_app$c',type,
    'fun_app$c': ( 'Rows_bool_fun$' * 'Rows$' ) > $o ).

tff('to_nat$a',type,
    'to_nat$a': 'Rows$' > 'Nat$' ).

tff('dbl_inc$b',type,
    'dbl_inc$b': 'Rows$' > 'Rows$' ).

tff('zero$h',type,
    'zero$h': 'Real_cols_vec$' ).

tff('less$a',type,
    'less$a': 'Nat_nat_bool_fun_fun$' ).

tff('zero$b',type,
    'zero$b': 'A_rows_vec$' ).

tff('arcosh$',type,
    'arcosh$': $real > $real ).

tff('column$f',type,
    'column$f': ( 'Cols$' * 'Real_cols_vec_rows_vec$' ) > 'Real_rows_vec$' ).

tff('fun_app$l',type,
    'fun_app$l': ( 'Nat_nat_fun$' * 'Nat$' ) > 'Nat$' ).

tff('power$b',type,
    'power$b': $real > 'Nat_real_fun$' ).

tff('less_eq$a',type,
    'less_eq$a': 'Rows_rows_bool_fun_fun$' ).

tff('vec_nth$k',type,
    'vec_nth$k': ( 'A_rows_vec_rows_vec$' * 'Rows$' ) > 'A_rows_vec$' ).

tff('zero$',type,
    'zero$': 'Rows$' ).

tff('column$a',type,
    'column$a': ( 'Rows$' * 'Real_rows_vec_rows_vec$' ) > 'Real_rows_vec$' ).

tff('fun_app$e',type,
    'fun_app$e': ( 'Cols_a_fun$' * 'Cols$' ) > 'A$' ).

tff('of_nat$',type,
    'of_nat$': 'Nat_int_fun$' ).

tff('fun_app$a',type,
    'fun_app$a': ( 'Int_bool_fun$' * $int ) > $o ).

tff('dbl_inc$a',type,
    'dbl_inc$a': $int > $int ).

tff('vec_nth$o',type,
    'vec_nth$o': ( 'Int_cols_vec_rows_vec$' * 'Rows$' ) > 'Int_cols_vec$' ).

tff('reduced_row_echelon_form$e',type,
    'reduced_row_echelon_form$e': 'A_rows_vec_rows_vec$' > $o ).

tff('zero$e',type,
    'zero$e': 'Int_rows_vec$' ).

tff('dbl_inc$c',type,
    'dbl_inc$c': 'Cols$' > 'Cols$' ).

tff('column$g',type,
    'column$g': ( 'Cols$' * 'Int_cols_vec_rows_vec$' ) > 'Int_rows_vec$' ).

tff('fun_app$',type,
    'fun_app$': ( 'Real_bool_fun$' * $real ) > $o ).

tff('column$j',type,
    'column$j': ( 'Rows$' * 'Real_rows_vec_cols_vec$' ) > 'Real_cols_vec$' ).

tff('of_nat$a',type,
    'of_nat$a': 'Nat_real_fun$' ).

tff(tltrue,type,
    tltrue: tlbool ).

tff('dbl_inc$',type,
    'dbl_inc$': $real > $real ).

tff('ncols$',type,
    'ncols$': 'A_cols_vec_rows_vec$' > 'Nat$' ).

tff('vec_nth$g',type,
    'vec_nth$g': ( 'Rows_rows_vec_rows_vec$' * 'Rows$' ) > 'Rows_rows_vec$' ).

tff('to_nat$',type,
    'to_nat$': 'Cols$' > 'Nat$' ).

tff('one$d',type,
    'one$d': 'Cols$' ).

tff('uu$',type,
    'uu$': 'Real_set$' > 'Real_bool_fun$' ).

tff('a$',type,
    'a$': 'A_cols_vec_rows_vec$' ).

tff('fun_app$f',type,
    'fun_app$f': ( 'Rows_a_cols_vec_fun$' * 'Rows$' ) > 'A_cols_vec$' ).

tff('artanh$',type,
    'artanh$': $real > $real ).

tff('powr$',type,
    'powr$': ( $real * $real ) > $real ).

tff('vec_nth$t',type,
    'vec_nth$t': ( 'Real_rows_vec_cols_vec$' * 'Cols$' ) > 'Real_rows_vec$' ).

tff('vec$',type,
    'vec$': 'A$' > 'A_cols_vec$' ).

tff('zero$d',type,
    'zero$d': 'Real_rows_vec$' ).

tff('vec_nth$l',type,
    'vec_nth$l': ( 'Real_cols_vec$' * 'Cols$' ) > $real ).

tff('uub$',type,
    'uub$': $real > 'Real_bool_fun$' ).

tff('one$b',type,
    'one$b': 'A_cols_vec_rows_vec$' ).

tff('zero$a',type,
    'zero$a': 'Cols$' ).

tff('power$a',type,
    'power$a': $int > 'Nat_int_fun$' ).

tff('vec_nth$p',type,
    'vec_nth$p': ( 'Rows_cols_vec$' * 'Cols$' ) > 'Rows$' ).

tff('uminus$a',type,
    'uminus$a': 'Cols$' > 'Cols$' ).

tff('zero$j',type,
    'zero$j': 'A_cols_vec_rows_vec$' ).

tff('reduced_row_echelon_form$h',type,
    'reduced_row_echelon_form$h': 'Rows_cols_vec_rows_vec$' > $o ).

tff('fun_app$i',type,
    'fun_app$i': ( 'Nat_real_fun$' * 'Nat$' ) > $real ).

tff('vec_nth$r',type,
    'vec_nth$r': ( 'Cols_cols_vec$' * 'Cols$' ) > 'Cols$' ).

tff('column$e',type,
    'column$e': ( 'Rows$' * 'A_rows_vec_rows_vec$' ) > 'A_rows_vec$' ).

tff('map_matrix$',type,
    'map_matrix$': ( 'A_a_fun$' * 'A_cols_vec_rows_vec$' ) > 'A_cols_vec_rows_vec$' ).

tff('from_nat$',type,
    'from_nat$': 'Nat_rows_fun$' ).

tff('of_nat$b',type,
    'of_nat$b': 'Nat_nat_fun$' ).

tff('is_zero_row$',type,
    'is_zero_row$': ( 'Rows$' * 'A_cols_vec_rows_vec$' ) > $o ).

tff('from_nat$a',type,
    'from_nat$a': 'Nat$' > 'Cols$' ).

tff('fun_app$h',type,
    'fun_app$h': ( 'Nat_int_fun$' * 'Nat$' ) > $int ).

tff('fun_app$b',type,
    'fun_app$b': ( 'Nat_bool_fun$' * 'Nat$' ) > $o ).

tff('fun_app$g',type,
    'fun_app$g': ( 'A_a_fun$' * 'A$' ) > 'A$' ).

tff('reduced_row_echelon_form$j',type,
    'reduced_row_echelon_form$j': 'Real_rows_vec_cols_vec$' > $o ).

tff('vec_nth$a',type,
    'vec_nth$a': 'A_cols_vec_rows_vec$' > 'Rows_a_cols_vec_fun$' ).

tff('fun_app$j',type,
    'fun_app$j': ( 'Nat_rows_fun$' * 'Nat$' ) > 'Rows$' ).

tff('less_eq$b',type,
    'less_eq$b': ( 'Cols$' * 'Cols$' ) > $o ).

tff('less_eq$',type,
    'less_eq$': 'Nat_nat_bool_fun_fun$' ).

tff('zero$f',type,
    'zero$f': 'Rows_rows_vec$' ).

tff('zero$c',type,
    'zero$c': 'A$' ).

tff('vec_nth$m',type,
    'vec_nth$m': ( 'Real_cols_vec_rows_vec$' * 'Rows$' ) > 'Real_cols_vec$' ).

tff('i$',type,
    'i$': 'Rows$' ).

tff(tlfalse,type,
    tlfalse: tlbool ).

tff('nat$',type,
    'nat$': $int > 'Nat$' ).

tff('member$',type,
    'member$': ( $real * 'Real_set$' ) > $o ).

tff('arsinh$',type,
    'arsinh$': $real > $real ).

tff('less$',type,
    'less$': 'Rows_rows_bool_fun_fun$' ).

tff('reduced_row_echelon_form$',type,
    'reduced_row_echelon_form$': 'A_cols_vec_rows_vec$' > $o ).

tff('reduced_row_echelon_form$b',type,
    'reduced_row_echelon_form$b': 'Int_rows_vec_rows_vec$' > $o ).

tff('vec_nth$i',type,
    'vec_nth$i': ( 'Cols_rows_vec_rows_vec$' * 'Rows$' ) > 'Cols_rows_vec$' ).

tff('vec$a',type,
    'vec$a': 'A_cols_vec$' > 'A_cols_vec_rows_vec$' ).

tff('column$c',type,
    'column$c': ( 'Rows$' * 'Rows_rows_vec_rows_vec$' ) > 'Rows_rows_vec$' ).

tff('reduced_row_echelon_form$i',type,
    'reduced_row_echelon_form$i': 'Cols_cols_vec_rows_vec$' > $o ).

tff('uua$',type,
    'uua$': $int > 'Int_bool_fun$' ).

tff('reduced_row_echelon_form$a',type,
    'reduced_row_echelon_form$a': 'Real_rows_vec_rows_vec$' > $o ).

tff('zero$g',type,
    'zero$g': 'Cols_rows_vec$' ).

tff('axis$a',type,
    'axis$a': ( 'Rows$' * 'A_cols_vec$' ) > 'A_cols_vec_rows_vec$' ).

tff('zero$i',type,
    'zero$i': 'A_cols_vec$' ).

tff('reduced_row_echelon_form$d',type,
    'reduced_row_echelon_form$d': 'Cols_rows_vec_rows_vec$' > $o ).

tff('fun_app$k',type,
    'fun_app$k': ( 'Nat_nat_bool_fun_fun$' * 'Nat$' ) > 'Nat_bool_fun$' ).

tff('reduced_row_echelon_form_upt_k$',type,
    'reduced_row_echelon_form_upt_k$': 'A_cols_vec_rows_vec$' > 'Nat_bool_fun$' ).

tff('vec_nth$j',type,
    'vec_nth$j': ( 'A_rows_vec$' * 'Rows$' ) > 'A$' ).

tff('vec_nth$d',type,
    'vec_nth$d': ( 'Int_rows_vec$' * 'Rows$' ) > $int ).

tff('reduced_row_echelon_form$c',type,
    'reduced_row_echelon_form$c': 'Rows_rows_vec_rows_vec$' > $o ).

tff('vec_nth$q',type,
    'vec_nth$q': ( 'Rows_cols_vec_rows_vec$' * 'Rows$' ) > 'Rows_cols_vec$' ).

tff('vec_nth$h',type,
    'vec_nth$h': ( 'Cols_rows_vec$' * 'Rows$' ) > 'Cols$' ).

tff('column$i',type,
    'column$i': ( 'Cols$' * 'Cols_cols_vec_rows_vec$' ) > 'Cols_rows_vec$' ).

tff('vec_nth$f',type,
    'vec_nth$f': ( 'Rows_rows_vec$' * 'Rows$' ) > 'Rows$' ).

tff('ln$',type,
    'ln$': $real > $real ).

tff('collect$',type,
    'collect$': 'Real_bool_fun$' > 'Real_set$' ).

tff('power$',type,
    'power$': 'Nat$' > 'Nat_nat_fun$' ).

tff('uminus$',type,
    'uminus$': 'Rows$' > 'Rows$' ).

tff('one$',type,
    'one$': 'A_cols_vec$' ).

%% Assertions:
%% ∀ ?v0:Real ?v1:Real (fun_app$(uub$(?v0), ?v1) = (?v0 < ?v1))
tff(axiom0,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( 'fun_app$'('uub$'(A__questionmark_v0),A__questionmark_v1)
    <=> $less(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$a(uua$(?v0), ?v1) = (?v0 < ?v1))
tff(axiom1,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( 'fun_app$a'('uua$'(A__questionmark_v0),A__questionmark_v1)
    <=> $less(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Real_set$ ?v1:Real (fun_app$(uu$(?v0), ?v1) = member$(?v1, ?v0))
tff(axiom2,axiom,
    ! [A__questionmark_v0: 'Real_set$',A__questionmark_v1: $real] :
      ( 'fun_app$'('uu$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'member$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ¬¬reduced_row_echelon_form$(a$)
tff(conjecture3,conjecture,
    ~ 'reduced_row_echelon_form$'('a$') ).

%% ¬is_zero_row_upt_k$(i$, nat$(1), a$)
tff(axiom4,axiom,
    ~ 'is_zero_row_upt_k$'('i$','nat$'(1),'a$') ).

%% is_zero_row_upt_k$(zero$, nat$(1), a$)
tff(axiom5,axiom,
    'is_zero_row_upt_k$'('zero$','nat$'(1),'a$') ).

%% reduced_row_echelon_form$(a$)
tff(axiom6,axiom,
    'reduced_row_echelon_form$'('a$') ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:Nat$ (reduced_row_echelon_form$(?v0) ⇒ fun_app$b(reduced_row_echelon_form_upt_k$(?v0), ?v1))
tff(axiom7,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
     => 'fun_app$b'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1) ) ).

%% fun_app$c(fun_app$d(less$, zero$), i$)
tff(axiom8,axiom,
    'fun_app$c'('fun_app$d'('less$','zero$'),'i$') ).

%% ¬(column$(zero$a, a$) = zero$b)
tff(axiom9,axiom,
    'column$'('zero$a','a$') != 'zero$b' ).

%% ∀ ?v0:A_cols_vec_rows_vec$ (reduced_row_echelon_form$(?v0) = fun_app$b(reduced_row_echelon_form_upt_k$(?v0), ncols$(?v0)))
tff(axiom10,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
    <=> 'fun_app$b'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),'ncols$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ (reduced_row_echelon_form$(?v0) ⇒ ∀ ?v1:Rows$ (is_zero_row$(?v1, ?v0) ⇒ ¬∃ ?v2:Rows$ (fun_app$c(fun_app$d(less$, ?v1), ?v2) ∧ ¬is_zero_row$(?v2, ?v0))))
tff(axiom11,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$'] :
      ( 'reduced_row_echelon_form$'(A__questionmark_v0)
     => ! [A__questionmark_v1: 'Rows$'] :
          ( 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0)
         => ~ ? [A__questionmark_v2: 'Rows$'] :
                ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v2)
                & ~ 'is_zero_row$'(A__questionmark_v2,A__questionmark_v0) ) ) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:Rows$ ((reduced_row_echelon_form$(?v0) ∧ is_zero_row$(?v1, ?v0)) ⇒ ∀ ?v2:Rows$ (fun_app$c(fun_app$d(less$, ?v1), ?v2) ⇒ is_zero_row$(?v2, ?v0)))
tff(axiom12,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'Rows$'] :
      ( ( 'reduced_row_echelon_form$'(A__questionmark_v0)
        & 'is_zero_row$'(A__questionmark_v1,A__questionmark_v0) )
     => ! [A__questionmark_v2: 'Rows$'] :
          ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v2)
         => 'is_zero_row$'(A__questionmark_v2,A__questionmark_v0) ) ) ).

%% ¬(fun_app$e(vec_nth$(fun_app$f(vec_nth$a(a$), i$)), zero$a) = zero$c)
tff(axiom13,axiom,
    'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'('a$'),'i$')),'zero$a') != 'zero$c' ).

%% (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(a$), zero$)), zero$a) = zero$c)
tff(axiom14,axiom,
    'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'('a$'),'zero$')),'zero$a') = 'zero$c' ).

%% (∀ ?v0:Rows$ ((¬(fun_app$e(vec_nth$(fun_app$f(vec_nth$a(a$), ?v0)), zero$a) = zero$c) ∧ fun_app$c(fun_app$d(less$, zero$), ?v0)) ⇒ false) ⇒ false)
tff(axiom15,axiom,
    ( ! [A__questionmark_v0: 'Rows$'] :
        ( ( ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'('a$'),A__questionmark_v0)),'zero$a') != 'zero$c' )
          & 'fun_app$c'('fun_app$d'('less$','zero$'),A__questionmark_v0) )
       => $false )
   => $false ) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec_rows_vec$ (is_zero_row$(?v0, ?v1) = is_zero_row_upt_k$(?v0, ncols$(?v1), ?v1))
tff(axiom16,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
    <=> 'is_zero_row_upt_k$'(A__questionmark_v0,'ncols$'(A__questionmark_v1),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec_rows_vec$ (is_zero_row$(?v0, ?v1) = ∀ ?v2:Cols$ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v1), ?v0)), ?v2) = zero$c))
tff(axiom17,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v0)),A__questionmark_v2) = 'zero$c' ) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:Nat$ (fun_app$b(reduced_row_echelon_form_upt_k$(?v0), ?v1) ⇒ ∀ ?v2:Rows$ (is_zero_row_upt_k$(?v2, ?v1, ?v0) ⇒ ¬∃ ?v3:Rows$ (fun_app$c(fun_app$d(less$, ?v2), ?v3) ∧ ¬is_zero_row_upt_k$(?v3, ?v1, ?v0))))
tff(axiom18,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
     => ! [A__questionmark_v2: 'Rows$'] :
          ( 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
         => ~ ? [A__questionmark_v3: 'Rows$'] :
                ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v3)
                & ~ 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v1,A__questionmark_v0) ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec_rows_vec$ (is_zero_row_upt_k$(?v0, ncols$(?v1), ?v1) = ∀ ?v2:Cols$ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v1), ?v0)), ?v2) = zero$c))
tff(axiom19,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( 'is_zero_row_upt_k$'(A__questionmark_v0,'ncols$'(A__questionmark_v1),A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v0)),A__questionmark_v2) = 'zero$c' ) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:Nat$ ?v2:Rows$ ?v3:Rows$ ((fun_app$b(reduced_row_echelon_form_upt_k$(?v0), ?v1) ∧ (is_zero_row_upt_k$(?v2, ?v1, ?v0) ∧ fun_app$c(fun_app$d(less$, ?v2), ?v3))) ⇒ is_zero_row_upt_k$(?v3, ?v1, ?v0))
tff(axiom20,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Rows$',A__questionmark_v3: 'Rows$'] :
      ( ( 'fun_app$b'('reduced_row_echelon_form_upt_k$'(A__questionmark_v0),A__questionmark_v1)
        & 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v1,A__questionmark_v0)
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v3) )
     => 'is_zero_row_upt_k$'(A__questionmark_v3,A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec_rows_vec$ ?v2:Nat$ (is_zero_row$(?v0, ?v1) ⇒ is_zero_row_upt_k$(?v0, ?v2, ?v1))
tff(axiom21,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec_rows_vec$',A__questionmark_v2: 'Nat$'] :
      ( 'is_zero_row$'(A__questionmark_v0,A__questionmark_v1)
     => 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:A_cols_vec_rows_vec$ (∀ ?v2:Rows$ is_zero_row_upt_k$(?v2, ?v0, ?v1) ⇒ fun_app$b(reduced_row_echelon_form_upt_k$(?v1), ?v0))
tff(axiom22,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( ! [A__questionmark_v2: 'Rows$'] : 'is_zero_row_upt_k$'(A__questionmark_v2,A__questionmark_v0,A__questionmark_v1)
     => 'fun_app$b'('reduced_row_echelon_form_upt_k$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Real_rows_vec_rows_vec$ ((reduced_row_echelon_form$a(?v0) ∧ (vec_nth$b(vec_nth$c(?v0, zero$), zero$) = 0.0)) ⇒ (column$a(zero$, ?v0) = zero$d))
tff(axiom23,axiom,
    ! [A__questionmark_v0: 'Real_rows_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$a'(A__questionmark_v0)
        & ( 'vec_nth$b'('vec_nth$c'(A__questionmark_v0,'zero$'),'zero$') = 0.0 ) )
     => ( 'column$a'('zero$',A__questionmark_v0) = 'zero$d' ) ) ).

%% ∀ ?v0:Int_rows_vec_rows_vec$ ((reduced_row_echelon_form$b(?v0) ∧ (vec_nth$d(vec_nth$e(?v0, zero$), zero$) = 0)) ⇒ (column$b(zero$, ?v0) = zero$e))
tff(axiom24,axiom,
    ! [A__questionmark_v0: 'Int_rows_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$b'(A__questionmark_v0)
        & ( 'vec_nth$d'('vec_nth$e'(A__questionmark_v0,'zero$'),'zero$') = 0 ) )
     => ( 'column$b'('zero$',A__questionmark_v0) = 'zero$e' ) ) ).

%% ∀ ?v0:Rows_rows_vec_rows_vec$ ((reduced_row_echelon_form$c(?v0) ∧ (vec_nth$f(vec_nth$g(?v0, zero$), zero$) = zero$)) ⇒ (column$c(zero$, ?v0) = zero$f))
tff(axiom25,axiom,
    ! [A__questionmark_v0: 'Rows_rows_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$c'(A__questionmark_v0)
        & ( 'vec_nth$f'('vec_nth$g'(A__questionmark_v0,'zero$'),'zero$') = 'zero$' ) )
     => ( 'column$c'('zero$',A__questionmark_v0) = 'zero$f' ) ) ).

%% ∀ ?v0:Cols_rows_vec_rows_vec$ ((reduced_row_echelon_form$d(?v0) ∧ (vec_nth$h(vec_nth$i(?v0, zero$), zero$) = zero$a)) ⇒ (column$d(zero$, ?v0) = zero$g))
tff(axiom26,axiom,
    ! [A__questionmark_v0: 'Cols_rows_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$d'(A__questionmark_v0)
        & ( 'vec_nth$h'('vec_nth$i'(A__questionmark_v0,'zero$'),'zero$') = 'zero$a' ) )
     => ( 'column$d'('zero$',A__questionmark_v0) = 'zero$g' ) ) ).

%% ∀ ?v0:A_rows_vec_rows_vec$ ((reduced_row_echelon_form$e(?v0) ∧ (vec_nth$j(vec_nth$k(?v0, zero$), zero$) = zero$c)) ⇒ (column$e(zero$, ?v0) = zero$b))
tff(axiom27,axiom,
    ! [A__questionmark_v0: 'A_rows_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$e'(A__questionmark_v0)
        & ( 'vec_nth$j'('vec_nth$k'(A__questionmark_v0,'zero$'),'zero$') = 'zero$c' ) )
     => ( 'column$e'('zero$',A__questionmark_v0) = 'zero$b' ) ) ).

%% ∀ ?v0:Real_cols_vec_rows_vec$ ((reduced_row_echelon_form$f(?v0) ∧ (vec_nth$l(vec_nth$m(?v0, zero$), zero$a) = 0.0)) ⇒ (column$f(zero$a, ?v0) = zero$d))
tff(axiom28,axiom,
    ! [A__questionmark_v0: 'Real_cols_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$f'(A__questionmark_v0)
        & ( 'vec_nth$l'('vec_nth$m'(A__questionmark_v0,'zero$'),'zero$a') = 0.0 ) )
     => ( 'column$f'('zero$a',A__questionmark_v0) = 'zero$d' ) ) ).

%% ∀ ?v0:Int_cols_vec_rows_vec$ ((reduced_row_echelon_form$g(?v0) ∧ (vec_nth$n(vec_nth$o(?v0, zero$), zero$a) = 0)) ⇒ (column$g(zero$a, ?v0) = zero$e))
tff(axiom29,axiom,
    ! [A__questionmark_v0: 'Int_cols_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$g'(A__questionmark_v0)
        & ( 'vec_nth$n'('vec_nth$o'(A__questionmark_v0,'zero$'),'zero$a') = 0 ) )
     => ( 'column$g'('zero$a',A__questionmark_v0) = 'zero$e' ) ) ).

%% ∀ ?v0:Rows_cols_vec_rows_vec$ ((reduced_row_echelon_form$h(?v0) ∧ (vec_nth$p(vec_nth$q(?v0, zero$), zero$a) = zero$)) ⇒ (column$h(zero$a, ?v0) = zero$f))
tff(axiom30,axiom,
    ! [A__questionmark_v0: 'Rows_cols_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$h'(A__questionmark_v0)
        & ( 'vec_nth$p'('vec_nth$q'(A__questionmark_v0,'zero$'),'zero$a') = 'zero$' ) )
     => ( 'column$h'('zero$a',A__questionmark_v0) = 'zero$f' ) ) ).

%% ∀ ?v0:Cols_cols_vec_rows_vec$ ((reduced_row_echelon_form$i(?v0) ∧ (vec_nth$r(vec_nth$s(?v0, zero$), zero$a) = zero$a)) ⇒ (column$i(zero$a, ?v0) = zero$g))
tff(axiom31,axiom,
    ! [A__questionmark_v0: 'Cols_cols_vec_rows_vec$'] :
      ( ( 'reduced_row_echelon_form$i'(A__questionmark_v0)
        & ( 'vec_nth$r'('vec_nth$s'(A__questionmark_v0,'zero$'),'zero$a') = 'zero$a' ) )
     => ( 'column$i'('zero$a',A__questionmark_v0) = 'zero$g' ) ) ).

%% ∀ ?v0:Real_rows_vec_cols_vec$ ((reduced_row_echelon_form$j(?v0) ∧ (vec_nth$b(vec_nth$t(?v0, zero$a), zero$) = 0.0)) ⇒ (column$j(zero$, ?v0) = zero$h))
tff(axiom32,axiom,
    ! [A__questionmark_v0: 'Real_rows_vec_cols_vec$'] :
      ( ( 'reduced_row_echelon_form$j'(A__questionmark_v0)
        & ( 'vec_nth$b'('vec_nth$t'(A__questionmark_v0,'zero$a'),'zero$') = 0.0 ) )
     => ( 'column$j'('zero$',A__questionmark_v0) = 'zero$h' ) ) ).

%% ∀ ?v0:Cols$ (fun_app$e(vec_nth$(zero$i), ?v0) = zero$c)
tff(axiom33,axiom,
    ! [A__questionmark_v0: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('zero$i'),A__questionmark_v0) = 'zero$c' ) ).

%% ∀ ?v0:Rows$ (fun_app$f(vec_nth$a(zero$j), ?v0) = zero$i)
tff(axiom34,axiom,
    ! [A__questionmark_v0: 'Rows$'] : ( 'fun_app$f'('vec_nth$a'('zero$j'),A__questionmark_v0) = 'zero$i' ) ).

%% ∀ ?v0:Cols$ (fun_app$e(vec_nth$(one$), ?v0) = one$a)
tff(axiom35,axiom,
    ! [A__questionmark_v0: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('one$'),A__questionmark_v0) = 'one$a' ) ).

%% ∀ ?v0:Rows$ (fun_app$f(vec_nth$a(one$b), ?v0) = one$)
tff(axiom36,axiom,
    ! [A__questionmark_v0: 'Rows$'] : ( 'fun_app$f'('vec_nth$a'('one$b'),A__questionmark_v0) = 'one$' ) ).

%% (0 < 1)
tff(axiom37,axiom,
    $less(0,1) ).

%% (0.0 < 1.0)
tff(axiom38,axiom,
    $less(0.0,1.0) ).

%% (0 < 1)
tff(axiom39,axiom,
    $less(0,1) ).

%% (0.0 < 1.0)
tff(axiom40,axiom,
    $less(0.0,1.0) ).

%% ¬(1 < 0)
tff(axiom41,axiom,
    ~ $less(1,0) ).

%% ¬(1.0 < 0.0)
tff(axiom42,axiom,
    ~ $less(1.0,0.0) ).

%% ¬(1 < 1)
tff(axiom43,axiom,
    ~ $less(1,1) ).

%% ¬(1.0 < 1.0)
tff(axiom44,axiom,
    ~ $less(1.0,1.0) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:Rows$ is_zero_row_upt_k$(?v1, nat$(0), ?v0)
tff(axiom45,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'Rows$'] : 'is_zero_row_upt_k$'(A__questionmark_v1,'nat$'(0),A__questionmark_v0) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec_rows_vec$ is_zero_row_upt_k$(?v0, nat$(0), ?v1)
tff(axiom46,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] : 'is_zero_row_upt_k$'(A__questionmark_v0,'nat$'(0),A__questionmark_v1) ).

%% ∀ ?v0:Real ((0.0 = ?v0) = (?v0 = 0.0))
tff(axiom47,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( 0.0 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Int ((0 = ?v0) = (?v0 = 0))
tff(axiom48,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Rows$ ((zero$ = ?v0) = (?v0 = zero$))
tff(axiom49,axiom,
    ! [A__questionmark_v0: 'Rows$'] :
      ( ( 'zero$' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$' ) ) ).

%% ∀ ?v0:Cols$ ((zero$a = ?v0) = (?v0 = zero$a))
tff(axiom50,axiom,
    ! [A__questionmark_v0: 'Cols$'] :
      ( ( 'zero$a' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$a' ) ) ).

%% ∀ ?v0:A$ ((zero$c = ?v0) = (?v0 = zero$c))
tff(axiom51,axiom,
    ! [A__questionmark_v0: 'A$'] :
      ( ( 'zero$c' = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 'zero$c' ) ) ).

%% ∀ ?v0:Int ?v1:Int ((¬(?v0 = ?v1) ∧ (((?v0 < ?v1) ⇒ false) ∧ ((?v1 < ?v0) ⇒ false))) ⇒ false)
tff(axiom52,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( $less(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( $less(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Real ?v1:Real ((¬(?v0 = ?v1) ∧ (((?v0 < ?v1) ⇒ false) ∧ ((?v1 < ?v0) ⇒ false))) ⇒ false)
tff(axiom53,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( $less(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( $less(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ((1 = ?v0) = (?v0 = 1))
tff(axiom54,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 1 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 1 ) ) ).

%% ∀ ?v0:Real ((1.0 = ?v0) = (?v0 = 1.0))
tff(axiom55,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( 1.0 = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 1.0 ) ) ).

%% ∀ ?v0:Bool ?v1:A_cols_vec$ ?v2:A_cols_vec$ ?v3:Cols$ (fun_app$e(vec_nth$((if ?v0 ?v1 else ?v2)), ?v3) = (if ?v0 fun_app$e(vec_nth$(?v1), ?v3) else fun_app$e(vec_nth$(?v2), ?v3)))
tff(axiom56,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'A_cols_vec$',A__questionmark_v2: 'A_cols_vec$',A__questionmark_v3: 'Cols$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$e'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$e'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$e'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$e'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$e'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$e'('vec_nth$'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$e'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$e'('vec_nth$'(A__questionmark_v2),A__questionmark_v3) ) ) ) ) ) ).

%% ∀ ?v0:Bool ?v1:A_cols_vec_rows_vec$ ?v2:A_cols_vec_rows_vec$ ?v3:Rows$ (fun_app$f(vec_nth$a((if ?v0 ?v1 else ?v2)), ?v3) = (if ?v0 fun_app$f(vec_nth$a(?v1), ?v3) else fun_app$f(vec_nth$a(?v2), ?v3)))
tff(axiom57,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'A_cols_vec_rows_vec$',A__questionmark_v2: 'A_cols_vec_rows_vec$',A__questionmark_v3: 'Rows$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) = 'fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v3) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) = 'fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3) ) ) ) ) ) ).

%% ∀ ?v0:A_cols_vec$ ?v1:A_cols_vec$ ((?v0 = ?v1) = ∀ ?v2:Cols$ (fun_app$e(vec_nth$(?v0), ?v2) = fun_app$e(vec_nth$(?v1), ?v2)))
tff(axiom58,axiom,
    ! [A__questionmark_v0: 'A_cols_vec$',A__questionmark_v1: 'A_cols_vec$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ! [A__questionmark_v2: 'Cols$'] : ( 'fun_app$e'('vec_nth$'(A__questionmark_v0),A__questionmark_v2) = 'fun_app$e'('vec_nth$'(A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:A_cols_vec_rows_vec$ ((?v0 = ?v1) = ∀ ?v2:Rows$ (fun_app$f(vec_nth$a(?v0), ?v2) = fun_app$f(vec_nth$a(?v1), ?v2)))
tff(axiom59,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ! [A__questionmark_v2: 'Rows$'] : ( 'fun_app$f'('vec_nth$a'(A__questionmark_v0),A__questionmark_v2) = 'fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_cols_vec$ ?v1:A_cols_vec$ ((vec_nth$(?v0) = vec_nth$(?v1)) = (?v0 = ?v1))
tff(axiom60,axiom,
    ! [A__questionmark_v0: 'A_cols_vec$',A__questionmark_v1: 'A_cols_vec$'] :
      ( ( 'vec_nth$'(A__questionmark_v0) = 'vec_nth$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_cols_vec_rows_vec$ ?v1:A_cols_vec_rows_vec$ ((vec_nth$a(?v0) = vec_nth$a(?v1)) = (?v0 = ?v1))
tff(axiom61,axiom,
    ! [A__questionmark_v0: 'A_cols_vec_rows_vec$',A__questionmark_v1: 'A_cols_vec_rows_vec$'] :
      ( ( 'vec_nth$a'(A__questionmark_v0) = 'vec_nth$a'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Real ?v1:Real_bool_fun$ (member$(?v0, collect$(?v1)) = fun_app$(?v1, ?v0))
tff(axiom62,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Real_bool_fun$'] :
      ( 'member$'(A__questionmark_v0,'collect$'(A__questionmark_v1))
    <=> 'fun_app$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Real_set$ (collect$(uu$(?v0)) = ?v0)
tff(axiom63,axiom,
    ! [A__questionmark_v0: 'Real_set$'] : ( 'collect$'('uu$'(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ¬(0 < 0)
tff(axiom64,axiom,
    ~ $less(0,0) ).

%% ¬(0.0 < 0.0)
tff(axiom65,axiom,
    ~ $less(0.0,0.0) ).

%% ¬(0.0 = 1.0)
tff(axiom66,axiom,
    0.0 != 1.0 ).

%% ¬(0 = 1)
tff(axiom67,axiom,
    0 != 1 ).

%% ∀ ?v0:A_a_fun$ ?v1:A_cols_vec_rows_vec$ ?v2:Rows$ ?v3:Cols$ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(map_matrix$(?v0, ?v1)), ?v2)), ?v3) = fun_app$g(?v0, fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v1), ?v2)), ?v3)))
tff(axiom68,axiom,
    ! [A__questionmark_v0: 'A_a_fun$',A__questionmark_v1: 'A_cols_vec_rows_vec$',A__questionmark_v2: 'Rows$',A__questionmark_v3: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'('map_matrix$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2)),A__questionmark_v3) = 'fun_app$g'(A__questionmark_v0,'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v1),A__questionmark_v2)),A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) < 1) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom69,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),1)
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 < ?v0) ∧ (0.0 < ?v1)) ⇒ ∃ ?v2:Real ((0.0 < ?v2) ∧ ((?v2 < ?v0) ∧ (?v2 < ?v1))))
tff(axiom70,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(0.0,A__questionmark_v1) )
     => ? [A__questionmark_v2: $real] :
          ( $less(0.0,A__questionmark_v2)
          & $less(A__questionmark_v2,A__questionmark_v0)
          & $less(A__questionmark_v2,A__questionmark_v1) ) ) ).

%% (dbl_inc$(0.0) = 1.0)
tff(axiom71,axiom,
    'dbl_inc$'(0.0) = 1.0 ).

%% (dbl_inc$a(0) = 1)
tff(axiom72,axiom,
    'dbl_inc$a'(0) = 1 ).

%% (dbl_inc$b(zero$) = one$c)
tff(axiom73,axiom,
    'dbl_inc$b'('zero$') = 'one$c' ).

%% (dbl_inc$c(zero$a) = one$d)
tff(axiom74,axiom,
    'dbl_inc$c'('zero$a') = 'one$d' ).

%% ∀ ?v0:Rows$ ?v1:Nat$ ?v2:A_cols_vec_rows_vec$ (is_zero_row_upt_k$(?v0, ?v1, ?v2) = ∀ ?v3:Cols$ ((fun_app$h(of_nat$, to_nat$(?v3)) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v2), ?v0)), ?v3) = zero$c)))
tff(axiom75,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_cols_vec_rows_vec$'] :
      ( 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2)
    <=> ! [A__questionmark_v3: 'Cols$'] :
          ( $less('fun_app$h'('of_nat$','to_nat$'(A__questionmark_v3)),'fun_app$h'('of_nat$',A__questionmark_v1))
         => ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v0)),A__questionmark_v3) = 'zero$c' ) ) ) ).

%% (arcosh$(1.0) = 0.0)
tff(axiom76,axiom,
    'arcosh$'(1.0) = 0.0 ).

%% (1 = 1)
tff(axiom77,axiom,
    1 = 1 ).

%% ∀ ?v0:Nat$ (¬(fun_app$h(of_nat$, ?v0) = 0) = (0 < fun_app$h(of_nat$, ?v0)))
tff(axiom78,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
    <=> $less(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ (¬(fun_app$h(of_nat$, ?v0) = 0) = (0 < fun_app$h(of_nat$, ?v0)))
tff(axiom79,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
    <=> $less(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) < 0) = false)
tff(axiom80,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),0)
    <=> $false ) ).

%% ∀ ?v0:A$ ?v1:Cols$ (fun_app$e(vec_nth$(vec$(?v0)), ?v1) = ?v0)
tff(axiom81,axiom,
    ! [A__questionmark_v0: 'A$',A__questionmark_v1: 'Cols$'] : ( 'fun_app$e'('vec_nth$'('vec$'(A__questionmark_v0)),A__questionmark_v1) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_cols_vec$ ?v1:Rows$ (fun_app$f(vec_nth$a(vec$a(?v0)), ?v1) = ?v0)
tff(axiom82,axiom,
    ! [A__questionmark_v0: 'A_cols_vec$',A__questionmark_v1: 'Rows$'] : ( 'fun_app$f'('vec_nth$a'('vec$a'(A__questionmark_v0)),A__questionmark_v1) = A__questionmark_v0 ) ).

%% ∀ ?v0:Cols$ ?v1:A$ (fun_app$e(vec_nth$(axis$(?v0, ?v1)), ?v0) = ?v1)
tff(axiom83,axiom,
    ! [A__questionmark_v0: 'Cols$',A__questionmark_v1: 'A$'] : ( 'fun_app$e'('vec_nth$'('axis$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v1 ) ).

%% ∀ ?v0:Rows$ ?v1:A_cols_vec$ (fun_app$f(vec_nth$a(axis$a(?v0, ?v1)), ?v0) = ?v1)
tff(axiom84,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'A_cols_vec$'] : ( 'fun_app$f'('vec_nth$a'('axis$a'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v1 ) ).

%% ∀ ?v0:Nat$ ((((fun_app$h(of_nat$, ?v0) = 0) ⇒ false) ∧ (¬(fun_app$h(of_nat$, ?v0) = 0) ⇒ false)) ⇒ false)
tff(axiom85,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
         => $false ) )
     => $false ) ).

%% (0 = 0)
tff(axiom86,axiom,
    0 = 0 ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, ?v0) < 0)
tff(axiom87,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ (((fun_app$h(of_nat$, ?v0) = 0) ⇒ false) ⇒ (0 < fun_app$h(of_nat$, ?v0)))
tff(axiom88,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
       => $false )
     => $less(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ (¬(0 < fun_app$h(of_nat$, ?v0)) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom89,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ~ $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, ?v0) < 0)
tff(axiom90,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) < 0) ⇒ false)
tff(axiom91,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),0)
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ¬(fun_app$h(of_nat$, ?v1) = 0))
tff(axiom92,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$h'('of_nat$',A__questionmark_v1) != 0 ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$b(?v0, nat$(0)) ∧ ∀ ?v2:Nat$ (((0 < fun_app$h(of_nat$, ?v2)) ∧ ¬fun_app$b(?v0, ?v2)) ⇒ ∃ ?v3:Nat$ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v2)) ∧ ¬fun_app$b(?v0, ?v3)))) ⇒ fun_app$b(?v0, ?v1))
tff(axiom93,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,'nat$'(0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v2))
              & ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) )
           => ? [A__questionmark_v3: 'Nat$'] :
                ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2))
                & ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) ) ) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((¬(fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) ∧ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v0)) ⇒ false))) ⇒ false)
tff(axiom94,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 'fun_app$h'('of_nat$',A__questionmark_v1) )
        & ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
         => $false )
        & ( $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v0))
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (¬fun_app$b(?v0, ?v2) ⇒ ∃ ?v3:Nat$ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v2)) ∧ ¬fun_app$b(?v0, ?v3))) ⇒ fun_app$b(?v0, ?v1))
tff(axiom95,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v2)
         => ? [A__questionmark_v3: 'Nat$'] :
              ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2))
              & ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) ) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v2)) ⇒ fun_app$b(?v0, ?v3)) ⇒ fun_app$b(?v0, ?v2)) ⇒ fun_app$b(?v0, ?v1))
tff(axiom96,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ! [A__questionmark_v3: 'Nat$'] :
              ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2))
             => 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v0)) ⇒ false)
tff(axiom97,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v0))
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ¬(fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom98,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ¬(fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v0)))
tff(axiom99,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ( 'fun_app$h'('of_nat$',A__questionmark_v1) != 'fun_app$h'('of_nat$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v0))
tff(axiom100,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v0))))
tff(axiom101,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        | $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v0)) ) ) ).

%% (arsinh$(0.0) = 0.0)
tff(axiom102,axiom,
    'arsinh$'(0.0) = 0.0 ).

%% (artanh$(0.0) = 0.0)
tff(axiom103,axiom,
    'artanh$'(0.0) = 0.0 ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ (fun_app$h(of_nat$, to_nat$a(?v0)) < fun_app$h(of_nat$, to_nat$a(?v1))))
tff(axiom104,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => $less('fun_app$h'('of_nat$','to_nat$a'(A__questionmark_v0)),'fun_app$h'('of_nat$','to_nat$a'(A__questionmark_v1))) ) ).

%% (fun_app$h(of_nat$, to_nat$a(zero$)) = 0)
tff(axiom105,axiom,
    'fun_app$h'('of_nat$','to_nat$a'('zero$')) = 0 ).

%% (fun_app$h(of_nat$, to_nat$(zero$a)) = 0)
tff(axiom106,axiom,
    'fun_app$h'('of_nat$','to_nat$'('zero$a')) = 0 ).

%% ∀ ?v0:Rows$ ((fun_app$h(of_nat$, to_nat$a(?v0)) = 0) = (?v0 = zero$))
tff(axiom107,axiom,
    ! [A__questionmark_v0: 'Rows$'] :
      ( ( 'fun_app$h'('of_nat$','to_nat$a'(A__questionmark_v0)) = 0 )
    <=> ( A__questionmark_v0 = 'zero$' ) ) ).

%% ∀ ?v0:Cols$ ((fun_app$h(of_nat$, to_nat$(?v0)) = 0) = (?v0 = zero$a))
tff(axiom108,axiom,
    ! [A__questionmark_v0: 'Cols$'] :
      ( ( 'fun_app$h'('of_nat$','to_nat$'(A__questionmark_v0)) = 0 )
    <=> ( A__questionmark_v0 = 'zero$a' ) ) ).

%% (ln$(1.0) = 0.0)
tff(axiom109,axiom,
    'ln$'(1.0) = 0.0 ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) = (0 < fun_app$h(of_nat$, ?v0)))
tff(axiom110,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
    <=> $less(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ((0.0 < fun_app$i(of_nat$a, ?v0)) = (0 < fun_app$h(of_nat$, ?v0)))
tff(axiom111,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0.0,'fun_app$i'('of_nat$a',A__questionmark_v0))
    <=> $less(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom112,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$i(of_nat$a, ?v0) = fun_app$i(of_nat$a, ?v1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom113,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$i'('of_nat$a',A__questionmark_v0) = 'fun_app$i'('of_nat$a',A__questionmark_v1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) = 0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom114,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$i(of_nat$a, ?v0) = 0.0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom115,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$i'('of_nat$a',A__questionmark_v0) = 0.0 )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((0 = fun_app$h(of_nat$, ?v0)) = (0 = fun_app$h(of_nat$, ?v0)))
tff(axiom116,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 0 = 'fun_app$h'('of_nat$',A__questionmark_v0) )
    <=> ( 0 = 'fun_app$h'('of_nat$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ((0.0 = fun_app$i(of_nat$a, ?v0)) = (0 = fun_app$h(of_nat$, ?v0)))
tff(axiom117,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 0.0 = 'fun_app$i'('of_nat$a',A__questionmark_v0) )
    <=> ( 0 = 'fun_app$h'('of_nat$',A__questionmark_v0) ) ) ).

%% (fun_app$h(of_nat$, nat$(0)) = 0)
tff(axiom118,axiom,
    'fun_app$h'('of_nat$','nat$'(0)) = 0 ).

%% (fun_app$i(of_nat$a, nat$(0)) = 0.0)
tff(axiom119,axiom,
    'fun_app$i'('of_nat$a','nat$'(0)) = 0.0 ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom120,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$i(of_nat$a, ?v0) < fun_app$i(of_nat$a, ?v1)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom121,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('of_nat$a',A__questionmark_v1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) = 1) = (fun_app$h(of_nat$, ?v0) = 1))
tff(axiom122,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 1 )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$i(of_nat$a, ?v0) = 1.0) = (fun_app$h(of_nat$, ?v0) = 1))
tff(axiom123,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$i'('of_nat$a',A__questionmark_v0) = 1.0 )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% ∀ ?v0:Nat$ ((1 = fun_app$h(of_nat$, ?v0)) = (fun_app$h(of_nat$, ?v0) = 1))
tff(axiom124,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 1 = 'fun_app$h'('of_nat$',A__questionmark_v0) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% ∀ ?v0:Nat$ ((1.0 = fun_app$i(of_nat$a, ?v0)) = (fun_app$h(of_nat$, ?v0) = 1))
tff(axiom125,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 1.0 = 'fun_app$i'('of_nat$a',A__questionmark_v0) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 1 ) ) ).

%% (fun_app$h(of_nat$, nat$(1)) = 1)
tff(axiom126,axiom,
    'fun_app$h'('of_nat$','nat$'(1)) = 1 ).

%% (fun_app$i(of_nat$a, nat$(1)) = 1.0)
tff(axiom127,axiom,
    'fun_app$i'('of_nat$a','nat$'(1)) = 1.0 ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, ?v0) < 0)
tff(axiom128,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),0) ).

%% ∀ ?v0:Nat$ ¬(fun_app$i(of_nat$a, ?v0) < 0.0)
tff(axiom129,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $less('fun_app$i'('of_nat$a',A__questionmark_v0),0.0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom130,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$i(of_nat$a, ?v0) < fun_app$i(of_nat$a, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom131,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('of_nat$a',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom132,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$i(of_nat$a, ?v0) < fun_app$i(of_nat$a, ?v1)))
tff(axiom133,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('of_nat$a',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ((1 < fun_app$h(of_nat$, ?v0)) ⇒ (1 < fun_app$h(of_nat$, ?v0)))
tff(axiom134,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(1,'fun_app$h'('of_nat$',A__questionmark_v0))
     => $less(1,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ((1.0 < fun_app$i(of_nat$a, ?v0)) ⇒ (1 < fun_app$h(of_nat$, ?v0)))
tff(axiom135,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(1.0,'fun_app$i'('of_nat$a',A__questionmark_v0))
     => $less(1,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ((0 < ?v0) ⇒ ∃ ?v1:Nat$ ((0 < fun_app$h(of_nat$, ?v1)) ∧ (?v0 = fun_app$h(of_nat$, ?v1))))
tff(axiom136,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,A__questionmark_v0)
     => ? [A__questionmark_v1: 'Nat$'] :
          ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v1))
          & ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Int (((0 < ?v0) ∧ ∀ ?v1:Nat$ (((?v0 = fun_app$h(of_nat$, ?v1)) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom137,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $less(0,A__questionmark_v0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
              & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Real ∃ ?v1:Nat$ (?v0 < fun_app$i(of_nat$a, ?v1))
tff(axiom138,axiom,
    ! [A__questionmark_v0: $real] :
    ? [A__questionmark_v1: 'Nat$'] : $less(A__questionmark_v0,'fun_app$i'('of_nat$a',A__questionmark_v1)) ).

%% ∀ ?v0:Rows$ ?v1:Nat$ (fun_app$c(fun_app$d(less$, ?v0), fun_app$j(from_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, to_nat$a(?v0)) < fun_app$h(of_nat$, ?v1)))
tff(axiom139,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),'fun_app$j'('from_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$','to_nat$a'(A__questionmark_v0)),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$b(fun_app$k(less$a, zero$k), fun_app$l(power$(fun_app$l(of_nat$b, ?v0)), ?v1)) = ((0 < fun_app$h(of_nat$, ?v0)) ∨ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom140,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','zero$k'),'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v0)),A__questionmark_v1))
    <=> ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((0 < fun_app$h(power$a(fun_app$h(of_nat$, ?v0)), ?v1)) = ((0 < fun_app$h(of_nat$, ?v0)) ∨ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom141,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less(0,'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v0)),A__questionmark_v1))
    <=> ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((0.0 < fun_app$i(power$b(fun_app$i(of_nat$a, ?v0)), ?v1)) = ((0 < fun_app$h(of_nat$, ?v0)) ∨ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom142,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less(0.0,'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v0)),A__questionmark_v1))
    <=> ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Real (powr$(?v0, 0.0) = (if (?v0 = 0.0) 0.0 else 1.0))
tff(axiom143,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( ( A__questionmark_v0 = 0.0 )
       => ( 'powr$'(A__questionmark_v0,0.0) = 0.0 ) )
      & ( ( A__questionmark_v0 != 0.0 )
       => ( 'powr$'(A__questionmark_v0,0.0) = 1.0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) = (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom144,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) = (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom145,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(one$e), ?v0) = one$e)
tff(axiom146,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$l'('power$'('one$e'),A__questionmark_v0) = 'one$e' ) ).

%% ∀ ?v0:Nat$ (fun_app$i(power$b(1.0), ?v0) = 1.0)
tff(axiom147,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$i'('power$b'(1.0),A__questionmark_v0) = 1.0 ) ).

%% ∀ ?v0:Nat$ (fun_app$h(power$a(1), ?v0) = 1)
tff(axiom148,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('power$a'(1),A__questionmark_v0) = 1 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) = (0 + 1)) = ((fun_app$h(of_nat$, ?v1) = 0) ∨ (fun_app$h(of_nat$, ?v0) = (0 + 1))))
tff(axiom149,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = $sum(0,1) )
    <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 )
        | ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum(0,1) ) ) ) ).

%% ∀ ?v0:Nat$ (fun_app$h(of_nat$, fun_app$l(power$(nat$((0 + 1))), ?v0)) = (0 + 1))
tff(axiom150,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('of_nat$','fun_app$l'('power$'('nat$'($sum(0,1))),A__questionmark_v0)) = $sum(0,1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((0 < fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1))) = ((0 < fun_app$h(of_nat$, ?v0)) ∨ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom151,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)))
    <=> ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$l(of_nat$b, ?v0) = fun_app$l(power$(fun_app$l(of_nat$b, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom152,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$l'('of_nat$b',A__questionmark_v0) = 'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v1)),A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(of_nat$, ?v0) = fun_app$h(power$a(fun_app$h(of_nat$, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom153,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v1)),A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(of_nat$a, ?v0) = fun_app$i(power$b(fun_app$i(of_nat$a, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom154,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$i'('of_nat$a',A__questionmark_v0) = 'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v1)),A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$l(power$(fun_app$l(of_nat$b, ?v0)), ?v1) = fun_app$l(of_nat$b, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) = fun_app$h(of_nat$, ?v2)))
tff(axiom155,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v0)),A__questionmark_v1) = 'fun_app$l'('of_nat$b',A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(power$a(fun_app$h(of_nat$, ?v0)), ?v1) = fun_app$h(of_nat$, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) = fun_app$h(of_nat$, ?v2)))
tff(axiom156,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v0)),A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(power$b(fun_app$i(of_nat$a, ?v0)), ?v1) = fun_app$i(of_nat$a, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) = fun_app$h(of_nat$, ?v2)))
tff(axiom157,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v0)),A__questionmark_v1) = 'fun_app$i'('of_nat$a',A__questionmark_v2) )
    <=> ( 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$l(of_nat$b, fun_app$l(power$(?v0), ?v1)) = fun_app$l(power$(fun_app$l(of_nat$b, ?v0)), ?v1))
tff(axiom158,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$l'('of_nat$b','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v0)),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) = fun_app$h(power$a(fun_app$h(of_nat$, ?v0)), ?v1))
tff(axiom159,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v0)),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$i(of_nat$a, fun_app$l(power$(?v0), ?v1)) = fun_app$i(power$b(fun_app$i(of_nat$a, ?v0)), ?v1))
tff(axiom160,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ( 'fun_app$i'('of_nat$a','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v0)),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) < (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom161,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ((fun_app$h(of_nat$, ?v0) + 1) < (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom162,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ (fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom163,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1)) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(?v0), nat$(1)) = ?v0)
tff(axiom164,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$l'('power$'(A__questionmark_v0),'nat$'(1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Real (fun_app$i(power$b(?v0), nat$(1)) = ?v0)
tff(axiom165,axiom,
    ! [A__questionmark_v0: $real] : ( 'fun_app$i'('power$b'(A__questionmark_v0),'nat$'(1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$h(power$a(?v0), nat$(1)) = ?v0)
tff(axiom166,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$h'('power$a'(A__questionmark_v0),'nat$'(1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Real (powr$(0.0, ?v0) = 0.0)
tff(axiom167,axiom,
    ! [A__questionmark_v0: $real] : ( 'powr$'(0.0,A__questionmark_v0) = 0.0 ) ).

%% ∀ ?v0:Real ?v1:Real ((powr$(?v0, ?v1) = 0.0) = (?v0 = 0.0))
tff(axiom168,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( 'powr$'(A__questionmark_v0,A__questionmark_v1) = 0.0 )
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Real (powr$(1.0, ?v0) = 1.0)
tff(axiom169,axiom,
    ! [A__questionmark_v0: $real] : ( 'powr$'(1.0,A__questionmark_v0) = 1.0 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less$a, one$e), ?v0) ⇒ ((fun_app$l(power$(?v0), ?v1) = fun_app$l(power$(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v2))))
tff(axiom170,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
     => ( ( 'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2) )
      <=> ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ ((1 < ?v0) ⇒ ((fun_app$h(power$a(?v0), ?v1) = fun_app$h(power$a(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v2))))
tff(axiom171,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1,A__questionmark_v0)
     => ( ( 'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2) )
      <=> ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ ((1.0 < ?v0) ⇒ ((fun_app$i(power$b(?v0), ?v1) = fun_app$i(power$b(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v2))))
tff(axiom172,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1.0,A__questionmark_v0)
     => ( ( 'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2) )
      <=> ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(zero$k), nat$((fun_app$h(of_nat$, ?v0) + 1))) = zero$k)
tff(axiom173,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$l'('power$'('zero$k'),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))) = 'zero$k' ) ).

%% ∀ ?v0:Nat$ (fun_app$i(power$b(0.0), nat$((fun_app$h(of_nat$, ?v0) + 1))) = 0.0)
tff(axiom174,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$i'('power$b'(0.0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))) = 0.0 ) ).

%% ∀ ?v0:Nat$ (fun_app$h(power$a(0), nat$((fun_app$h(of_nat$, ?v0) + 1))) = 0)
tff(axiom175,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('power$a'(0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))) = 0 ) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(?v0), nat$((0 + 1))) = ?v0)
tff(axiom176,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$l'('power$'(A__questionmark_v0),'nat$'($sum(0,1))) = A__questionmark_v0 ) ).

%% ∀ ?v0:Real (fun_app$i(power$b(?v0), nat$((0 + 1))) = ?v0)
tff(axiom177,axiom,
    ! [A__questionmark_v0: $real] : ( 'fun_app$i'('power$b'(A__questionmark_v0),'nat$'($sum(0,1))) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$h(power$a(?v0), nat$((0 + 1))) = ?v0)
tff(axiom178,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$h'('power$a'(A__questionmark_v0),'nat$'($sum(0,1))) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) < (0 + 1)) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom179,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum(0,1))
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ (0 < (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom180,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less(0,$sum('fun_app$h'('of_nat$',A__questionmark_v0),1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less$a, one$e), ?v0) ⇒ (fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom181,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
     => ( 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ ((1 < ?v0) ⇒ ((fun_app$h(power$a(?v0), ?v1) < fun_app$h(power$a(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom182,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1,A__questionmark_v0)
     => ( $less('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ ((1.0 < ?v0) ⇒ ((fun_app$i(power$b(?v0), ?v1) < fun_app$i(power$b(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom183,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1.0,A__questionmark_v0)
     => ( $less('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$l(power$(?v0), ?v1) = zero$k) = ((?v0 = zero$k) ∧ (0 < fun_app$h(of_nat$, ?v1))))
tff(axiom184,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1) = 'zero$k' )
    <=> ( ( A__questionmark_v0 = 'zero$k' )
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((fun_app$i(power$b(?v0), ?v1) = 0.0) = ((?v0 = 0.0) ∧ (0 < fun_app$h(of_nat$, ?v1))))
tff(axiom185,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1) = 0.0 )
    <=> ( ( A__questionmark_v0 = 0.0 )
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((fun_app$h(power$a(?v0), ?v1) = 0) = ((?v0 = 0) ∧ (0 < fun_app$h(of_nat$, ?v1))))
tff(axiom186,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1) = 0 )
    <=> ( ( A__questionmark_v0 = 0 )
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less$a, fun_app$l(power$(fun_app$l(of_nat$b, ?v0)), ?v1)), fun_app$l(of_nat$b, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) < fun_app$h(of_nat$, ?v2)))
tff(axiom187,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v0)),A__questionmark_v1)),'fun_app$l'('of_nat$b',A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(power$a(fun_app$h(of_nat$, ?v0)), ?v1) < fun_app$h(of_nat$, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) < fun_app$h(of_nat$, ?v2)))
tff(axiom188,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v0)),A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(power$b(fun_app$i(of_nat$a, ?v0)), ?v1) < fun_app$i(of_nat$a, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) < fun_app$h(of_nat$, ?v2)))
tff(axiom189,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v0)),A__questionmark_v1),'fun_app$i'('of_nat$a',A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less$a, fun_app$l(of_nat$b, ?v0)), fun_app$l(power$(fun_app$l(of_nat$b, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom190,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('of_nat$b',A__questionmark_v0)),'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v1)),A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(power$a(fun_app$h(of_nat$, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom191,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v1)),A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(of_nat$a, ?v0) < fun_app$i(power$b(fun_app$i(of_nat$a, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom192,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v1)),A__questionmark_v2))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less$a, zero$k), ?v0) ∧ fun_app$b(fun_app$k(less$a, ?v0), one$e)) ⇒ (fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1))))
tff(axiom193,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','zero$k'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less$a',A__questionmark_v0),'one$e') )
     => ( 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ (((0 < ?v0) ∧ (?v0 < 1)) ⇒ ((fun_app$h(power$a(?v0), ?v1) < fun_app$h(power$a(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1))))
tff(axiom194,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(0,A__questionmark_v0)
        & $less(A__questionmark_v0,1) )
     => ( $less('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ (((0.0 < ?v0) ∧ (?v0 < 1.0)) ⇒ ((fun_app$i(power$b(?v0), ?v1) < fun_app$i(power$b(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1))))
tff(axiom195,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(A__questionmark_v0,1.0) )
     => ( $less('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom196,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ((¬fun_app$b(?v0, nat$(0)) ∧ ∃ ?v1:Nat$ fun_app$b(?v0, ?v1)) ⇒ ∃ ?v1:Nat$ (¬fun_app$b(?v0, ?v1) ∧ fun_app$b(?v0, nat$((fun_app$h(of_nat$, ?v1) + 1)))))
tff(axiom197,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ( ~ 'fun_app$b'(A__questionmark_v0,'nat$'(0))
        & ? [A__questionmark_v1: 'Nat$'] : 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) )
     => ? [A__questionmark_v1: 'Nat$'] :
          ( ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
          & 'fun_app$b'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1))) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$b(fun_app$k(less$a, one$e), ?v0) ⇒ fun_app$b(fun_app$k(less$a, one$e), fun_app$l(power$(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1)))))
tff(axiom198,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
     => 'fun_app$b'('fun_app$k'('less$a','one$e'),'fun_app$l'('power$'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((1 < ?v0) ⇒ (1 < fun_app$h(power$a(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1)))))
tff(axiom199,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $less(1,A__questionmark_v0)
     => $less(1,'fun_app$h'('power$a'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((1.0 < ?v0) ⇒ (1.0 < fun_app$i(power$b(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1)))))
tff(axiom200,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $less(1.0,A__questionmark_v0)
     => $less(1.0,'fun_app$i'('power$b'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((0 + 1) < fun_app$h(of_nat$, ?v0)) ⇒ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1))))
tff(axiom201,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum(0,1),'fun_app$h'('of_nat$',A__questionmark_v0))
     => $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(?v0 = zero$k) ⇒ ¬(fun_app$l(power$(?v0), ?v1) = zero$k))
tff(axiom202,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 != 'zero$k' )
     => ( 'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1) != 'zero$k' ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ (¬(?v0 = 0.0) ⇒ ¬(fun_app$i(power$b(?v0), ?v1) = 0.0))
tff(axiom203,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 != 0.0 )
     => ( 'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1) != 0.0 ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ (¬(?v0 = 0) ⇒ ¬(fun_app$h(power$a(?v0), ?v1) = 0))
tff(axiom204,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 != 0 )
     => ( 'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1) != 0 ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom205,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v0) != $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) = (fun_app$h(of_nat$, ?v1) + 1)) ⇒ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom206,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
     => ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% (0 = 0)
tff(axiom207,axiom,
    0 = 0 ).

%% ((0 < 0) = false)
tff(axiom208,axiom,
    ( $less(0,0)
  <=> $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$b(fun_app$k(less$a, zero$k), ?v0) ∧ fun_app$b(fun_app$k(less$a, ?v0), one$e)) ⇒ fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1)))), one$e))
tff(axiom209,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','zero$k'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less$a',A__questionmark_v0),'one$e') )
     => 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))),'one$e') ) ).

%% ∀ ?v0:Int ?v1:Nat$ (((0 < ?v0) ∧ (?v0 < 1)) ⇒ (fun_app$h(power$a(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1))) < 1))
tff(axiom210,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( ( $less(0,A__questionmark_v0)
        & $less(A__questionmark_v0,1) )
     => $less('fun_app$h'('power$a'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1))),1) ) ).

%% ∀ ?v0:Real ?v1:Nat$ (((0.0 < ?v0) ∧ (?v0 < 1.0)) ⇒ (fun_app$i(power$b(?v0), nat$((fun_app$h(of_nat$, ?v1) + 1))) < 1.0))
tff(axiom211,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(A__questionmark_v0,1.0) )
     => $less('fun_app$i'('power$b'(A__questionmark_v0),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1))),1.0) ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom212,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ¬((fun_app$h(of_nat$, ?v0) + 1) = 0)
tff(axiom213,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) != 0 ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom214,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)) ⇒ ¬(fun_app$h(of_nat$, ?v0) = 0))
tff(axiom215,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
     => ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 ) ) ).

%% ∀ ?v0:Nat$ ((((fun_app$h(of_nat$, ?v0) = 0) ⇒ false) ∧ ∀ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)) ⇒ false)) ⇒ false)
tff(axiom216,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$b(?v0, nat$(0)) ∧ ∀ ?v2:Nat$ (fun_app$b(?v0, ?v2) ⇒ fun_app$b(?v0, nat$((fun_app$h(of_nat$, ?v2) + 1))))) ⇒ fun_app$b(?v0, ?v1))
tff(axiom217,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,'nat$'(0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v2)
           => 'fun_app$b'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))) ) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$b(fun_app$k(?v0, ?v3), nat$(0)) ∧ (∀ ?v3:Nat$ fun_app$b(fun_app$k(?v0, nat$(0)), nat$((fun_app$h(of_nat$, ?v3) + 1))) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (fun_app$b(fun_app$k(?v0, ?v3), ?v4) ⇒ fun_app$b(fun_app$k(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1))), nat$((fun_app$h(of_nat$, ?v4) + 1)))))) ⇒ fun_app$b(fun_app$k(?v0, ?v1), ?v2))
tff(axiom218,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$b'('fun_app$k'(A__questionmark_v0,A__questionmark_v3),'nat$'(0))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$b'('fun_app$k'(A__questionmark_v0,'nat$'(0)),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1)))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$b'('fun_app$k'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$b'('fun_app$k'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v4),1))) ) )
     => 'fun_app$b'('fun_app$k'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$b(?v0, ?v1) ∧ ∀ ?v2:Nat$ (fun_app$b(?v0, nat$((fun_app$h(of_nat$, ?v2) + 1))) ⇒ fun_app$b(?v0, ?v2))) ⇒ fun_app$b(?v0, nat$(0)))
tff(axiom219,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( 'fun_app$b'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1)))
           => 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) ) )
     => 'fun_app$b'(A__questionmark_v0,'nat$'(0)) ) ).

%% ∀ ?v0:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) = 0) ⇒ false)
tff(axiom220,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) = 0 )
     => $false ) ).

%% ∀ ?v0:Nat$ ((0 = (fun_app$h(of_nat$, ?v0) + 1)) ⇒ false)
tff(axiom221,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 0 = $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) )
     => $false ) ).

%% ∀ ?v0:Nat$ ¬(0 = (fun_app$h(of_nat$, ?v0) + 1))
tff(axiom222,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 0 != $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ (¬(fun_app$h(of_nat$, ?v0) = 0) ⇒ ∃ ?v1:Nat$ (fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom223,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
     => ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ((fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))))
tff(axiom224,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
      <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v3) + 1)) ⇒ fun_app$b(?v2, ?v3)) ∧ ∀ ?v3:Nat$ (((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v1)) ∧ fun_app$b(?v2, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ⇒ fun_app$b(?v2, ?v3)))) ⇒ fun_app$b(?v2, ?v0))
tff(axiom225,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v3),1) )
           => 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) )
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v1))
              & 'fun_app$b'(A__questionmark_v2,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))) )
           => 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) ) )
     => 'fun_app$b'(A__questionmark_v2,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_bool_fun_fun$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ fun_app$b(fun_app$k(?v2, ?v3), nat$((fun_app$h(of_nat$, ?v3) + 1))) ∧ ∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ (((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v4)) ∧ ((fun_app$h(of_nat$, ?v4) < fun_app$h(of_nat$, ?v5)) ∧ (fun_app$b(fun_app$k(?v2, ?v3), ?v4) ∧ fun_app$b(fun_app$k(?v2, ?v4), ?v5)))) ⇒ fun_app$b(fun_app$k(?v2, ?v3), ?v5)))) ⇒ fun_app$b(fun_app$k(?v2, ?v0), ?v1))
tff(axiom226,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1)))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v4))
              & $less('fun_app$h'('of_nat$',A__questionmark_v4),'fun_app$h'('of_nat$',A__questionmark_v5))
              & 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)
              & 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v4),A__questionmark_v5) )
           => 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5) ) )
     => 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))) ⇒ ((fun_app$h(of_nat$, ?v0) + 1) < fun_app$h(of_nat$, ?v2)))
tff(axiom227,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) < (fun_app$h(of_nat$, ?v1) + 1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom228,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((¬(fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1))) ⇒ (fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v0)))
tff(axiom229,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1)) )
     => ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) < fun_app$h(of_nat$, ?v1)) = ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v2) + 1)) ∧ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v2))))
tff(axiom230,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> ? [A__questionmark_v2: 'Nat$'] :
          ( ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v2),1) )
          & $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∀ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < (fun_app$h(of_nat$, ?v0) + 1)) ⇒ fun_app$b(?v1, ?v2)) = (fun_app$b(?v1, ?v0) ∧ ∀ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v0)) ⇒ fun_app$b(?v1, ?v2))))
tff(axiom231,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$h'('of_nat$',A__questionmark_v2),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1))
         => 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$b'(A__questionmark_v1,A__questionmark_v0)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v0))
           => 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v1) < (fun_app$h(of_nat$, ?v0) + 1)))
tff(axiom232,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)) = ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))))
tff(axiom233,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < (fun_app$h(of_nat$, ?v0) + 1)) ∧ fun_app$b(?v1, ?v2)) = (fun_app$b(?v1, ?v0) ∨ ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v0)) ∧ fun_app$b(?v1, ?v2))))
tff(axiom234,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$h'('of_nat$',A__questionmark_v2),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1))
          & 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$b'(A__questionmark_v1,A__questionmark_v0)
        | ? [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v0))
            & 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom235,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)) ∧ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) ⇒ false))) ⇒ false)
tff(axiom236,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
        & ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
         => $false )
        & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ ¬((fun_app$h(of_nat$, ?v0) + 1) = fun_app$h(of_nat$, ?v1))) ⇒ ((fun_app$h(of_nat$, ?v0) + 1) < fun_app$h(of_nat$, ?v1)))
tff(axiom237,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ( $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) != 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
     => $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((((fun_app$h(of_nat$, ?v0) + 1) < fun_app$h(of_nat$, ?v1)) ∧ ∀ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v2)) ∧ (fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v2) + 1))) ⇒ false)) ⇒ false)
tff(axiom238,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v2))
              & ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v2),1) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom239,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (((fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v0) + 1)) ⇒ false) ∧ ∀ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v2)) ∧ (fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v2) + 1))) ⇒ false))) ⇒ false)
tff(axiom240,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ( ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v0),1) )
         => $false )
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v2))
              & ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v2),1) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$b(fun_app$k(less$a, zero$k), ?v0) ⇒ fun_app$b(fun_app$k(less$a, zero$k), fun_app$l(power$(?v0), ?v1)))
tff(axiom241,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','zero$k'),A__questionmark_v0)
     => 'fun_app$b'('fun_app$k'('less$a','zero$k'),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 < ?v0) ⇒ (0 < fun_app$h(power$a(?v0), ?v1)))
tff(axiom242,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $less(0,A__questionmark_v0)
     => $less(0,'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((0.0 < ?v0) ⇒ (0.0 < fun_app$i(power$b(?v0), ?v1)))
tff(axiom243,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $less(0.0,A__questionmark_v0)
     => $less(0.0,'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(?v0), nat$(0)) = one$e)
tff(axiom244,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$l'('power$'(A__questionmark_v0),'nat$'(0)) = 'one$e' ) ).

%% ∀ ?v0:Real (fun_app$i(power$b(?v0), nat$(0)) = 1.0)
tff(axiom245,axiom,
    ! [A__questionmark_v0: $real] : ( 'fun_app$i'('power$b'(A__questionmark_v0),'nat$'(0)) = 1.0 ) ).

%% ∀ ?v0:Int (fun_app$h(power$a(?v0), nat$(0)) = 1)
tff(axiom246,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$h'('power$a'(A__questionmark_v0),'nat$'(0)) = 1 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((0 < fun_app$h(of_nat$, ?v0)) ∧ (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) < fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v2)))) ⇒ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2)))
tff(axiom247,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        & $less('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2))) )
     => $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Rows$ ?v1:Nat$ ?v2:A_cols_vec_rows_vec$ (is_zero_row_upt_k$(?v0, nat$((fun_app$h(of_nat$, ?v1) + 1)), ?v2) ⇒ is_zero_row_upt_k$(?v0, ?v1, ?v2))
tff(axiom248,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_cols_vec_rows_vec$'] :
      ( 'is_zero_row_upt_k$'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)),A__questionmark_v2)
     => 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ (fun_app$l(power$(zero$k), ?v0) = (if (fun_app$h(of_nat$, ?v0) = 0) one$e else zero$k))
tff(axiom249,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
       => ( 'fun_app$l'('power$'('zero$k'),A__questionmark_v0) = 'one$e' ) )
      & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
       => ( 'fun_app$l'('power$'('zero$k'),A__questionmark_v0) = 'zero$k' ) ) ) ).

%% ∀ ?v0:Nat$ (fun_app$i(power$b(0.0), ?v0) = (if (fun_app$h(of_nat$, ?v0) = 0) 1.0 else 0.0))
tff(axiom250,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
       => ( 'fun_app$i'('power$b'(0.0),A__questionmark_v0) = 1.0 ) )
      & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
       => ( 'fun_app$i'('power$b'(0.0),A__questionmark_v0) = 0.0 ) ) ) ).

%% ∀ ?v0:Nat$ (fun_app$h(power$a(0), ?v0) = (if (fun_app$h(of_nat$, ?v0) = 0) 1 else 0))
tff(axiom251,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
       => ( 'fun_app$h'('power$a'(0),A__questionmark_v0) = 1 ) )
      & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 0 )
       => ( 'fun_app$h'('power$a'(0),A__questionmark_v0) = 0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less$a, one$e), ?v0) ∧ fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2)))
tff(axiom252,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2)) )
     => $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ (((1 < ?v0) ∧ (fun_app$h(power$a(?v0), ?v1) < fun_app$h(power$a(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2)))
tff(axiom253,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(1,A__questionmark_v0)
        & $less('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2)) )
     => $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ (((1.0 < ?v0) ∧ (fun_app$i(power$b(?v0), ?v1) < fun_app$i(power$b(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2)))
tff(axiom254,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(1.0,A__questionmark_v0)
        & $less('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2)) )
     => $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ fun_app$b(fun_app$k(less$a, one$e), ?v2)) ⇒ fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v2), ?v0)), fun_app$l(power$(?v2), ?v1)))
tff(axiom255,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v2) )
     => 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v0)),'fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Int (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (1 < ?v2)) ⇒ (fun_app$h(power$a(?v2), ?v0) < fun_app$h(power$a(?v2), ?v1)))
tff(axiom256,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $int] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less(1,A__questionmark_v2) )
     => $less('fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v0),'fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Real (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (1.0 < ?v2)) ⇒ (fun_app$i(power$b(?v2), ?v0) < fun_app$i(power$b(?v2), ?v1)))
tff(axiom257,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $real] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less(1.0,A__questionmark_v2) )
     => $less('fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0),'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) ⇒ (fun_app$l(power$(zero$k), ?v0) = zero$k))
tff(axiom258,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
     => ( 'fun_app$l'('power$'('zero$k'),A__questionmark_v0) = 'zero$k' ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) ⇒ (fun_app$i(power$b(0.0), ?v0) = 0.0))
tff(axiom259,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
     => ( 'fun_app$i'('power$b'(0.0),A__questionmark_v0) = 0.0 ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) ⇒ (fun_app$h(power$a(0), ?v0) = 0))
tff(axiom260,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
     => ( 'fun_app$h'('power$a'(0),A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v0) + 1))) = 0)
tff(axiom261,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))) != 0 ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$i(of_nat$a, nat$((fun_app$h(of_nat$, ?v0) + 1))) = 0.0)
tff(axiom262,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$i'('of_nat$a','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))) != 0.0 ) ).

%% ∀ ?v0:Nat_rows_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v3)), fun_app$j(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ∧ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))) ⇒ fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v1)), fun_app$j(?v0, ?v2)))
tff(axiom263,axiom,
    ! [A__questionmark_v0: 'Nat_rows_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v3)),'fun_app$j'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
        & $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v1)),'fun_app$j'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$h(?v0, ?v3) < fun_app$h(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ∧ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$h(?v0, ?v1) < fun_app$h(?v0, ?v2)))
tff(axiom264,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$h'(A__questionmark_v0,A__questionmark_v3),'fun_app$h'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
        & $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $less('fun_app$h'(A__questionmark_v0,A__questionmark_v1),'fun_app$h'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_real_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$i(?v0, ?v3) < fun_app$i(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ∧ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$i(?v0, ?v1) < fun_app$i(?v0, ?v2)))
tff(axiom265,axiom,
    ! [A__questionmark_v0: 'Nat_real_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$i'(A__questionmark_v0,A__questionmark_v3),'fun_app$i'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
        & $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $less('fun_app$i'(A__questionmark_v0,A__questionmark_v1),'fun_app$i'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_rows_fun$ ?v1:Nat$ ?v2:Nat$ (∀ ?v3:Nat$ fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v3)), fun_app$j(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ⇒ (fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v1)), fun_app$j(?v0, ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom266,axiom,
    ! [A__questionmark_v0: 'Nat_rows_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v3)),'fun_app$j'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
     => ( 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v1)),'fun_app$j'(A__questionmark_v0,A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ (∀ ?v3:Nat$ (fun_app$h(?v0, ?v3) < fun_app$h(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ⇒ ((fun_app$h(?v0, ?v1) < fun_app$h(?v0, ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom267,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$h'(A__questionmark_v0,A__questionmark_v3),'fun_app$h'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
     => ( $less('fun_app$h'(A__questionmark_v0,A__questionmark_v1),'fun_app$h'(A__questionmark_v0,A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat_real_fun$ ?v1:Nat$ ?v2:Nat$ (∀ ?v3:Nat$ (fun_app$i(?v0, ?v3) < fun_app$i(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ⇒ ((fun_app$i(?v0, ?v1) < fun_app$i(?v0, ?v2)) = (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))))
tff(axiom268,axiom,
    ! [A__questionmark_v0: 'Nat_real_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ! [A__questionmark_v3: 'Nat$'] : $less('fun_app$i'(A__questionmark_v0,A__questionmark_v3),'fun_app$i'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
     => ( $less('fun_app$i'(A__questionmark_v0,A__questionmark_v1),'fun_app$i'(A__questionmark_v0,A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < (fun_app$h(of_nat$, ?v0) + 1)) ∧ fun_app$b(?v1, ?v2)) = (fun_app$b(?v1, nat$(0)) ∨ ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v0)) ∧ fun_app$b(?v1, nat$((fun_app$h(of_nat$, ?v2) + 1))))))
tff(axiom269,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$h'('of_nat$',A__questionmark_v2),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1))
          & 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$b'(A__questionmark_v1,'nat$'(0))
        | ? [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v0))
            & 'fun_app$b'(A__questionmark_v1,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))) ) ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) = ∃ ?v1:Nat$ (fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom270,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
    <=> ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∀ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < (fun_app$h(of_nat$, ?v0) + 1)) ⇒ fun_app$b(?v1, ?v2)) = (fun_app$b(?v1, nat$(0)) ∧ ∀ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v0)) ⇒ fun_app$b(?v1, nat$((fun_app$h(of_nat$, ?v2) + 1))))))
tff(axiom271,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$h'('of_nat$',A__questionmark_v2),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1))
         => 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$b'(A__questionmark_v1,'nat$'(0))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v0))
           => 'fun_app$b'(A__questionmark_v1,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))) ) ) ) ).

%% ∀ ?v0:Nat$ ((0 < fun_app$h(of_nat$, ?v0)) ⇒ ∃ ?v1:Nat$ (fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom272,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
     => ? [A__questionmark_v1: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)) = ((fun_app$h(of_nat$, ?v0) = 0) ∨ ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v2) + 1)) ∧ (fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1)))))
tff(axiom273,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
        | ? [A__questionmark_v2: 'Nat$'] :
            ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v2),1) )
            & $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ) ).

%% (1 = (0 + 1))
tff(axiom274,axiom,
    1 = $sum(0,1) ).

%% ∀ ?v0:Rows$ ?v1:Nat$ ?v2:A_cols_vec_rows_vec$ ((is_zero_row_upt_k$(?v0, ?v1, ?v2) ∧ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v2), ?v0)), from_nat$a(?v1)) = zero$c)) ⇒ is_zero_row_upt_k$(?v0, nat$((fun_app$h(of_nat$, ?v1) + 1)), ?v2))
tff(axiom275,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_cols_vec_rows_vec$'] :
      ( ( 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2)
        & ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v0)),'from_nat$a'(A__questionmark_v1)) = 'zero$c' ) )
     => 'is_zero_row_upt_k$'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)),A__questionmark_v2) ) ).

%% ∀ ?v0:Rows$ ?v1:Nat$ ?v2:A_cols_vec_rows_vec$ ((¬is_zero_row_upt_k$(?v0, nat$((fun_app$h(of_nat$, ?v1) + 1)), ?v2) ∧ ∀ ?v3:Rows$ (fun_app$e(vec_nth$(fun_app$f(vec_nth$a(?v2), ?v3)), from_nat$a(?v1)) = zero$c)) ⇒ ¬is_zero_row_upt_k$(?v0, ?v1, ?v2))
tff(axiom276,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_cols_vec_rows_vec$'] :
      ( ( ~ 'is_zero_row_upt_k$'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)),A__questionmark_v2)
        & ! [A__questionmark_v3: 'Rows$'] : ( 'fun_app$e'('vec_nth$'('fun_app$f'('vec_nth$a'(A__questionmark_v2),A__questionmark_v3)),'from_nat$a'(A__questionmark_v1)) = 'zero$c' ) )
     => ~ 'is_zero_row_upt_k$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) ) ).

%% (fun_app$j(from_nat$, nat$(0)) = zero$)
tff(axiom277,axiom,
    'fun_app$j'('from_nat$','nat$'(0)) = 'zero$' ).

%% (from_nat$a(nat$(0)) = zero$a)
tff(axiom278,axiom,
    'from_nat$a'('nat$'(0)) = 'zero$a' ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ (fun_app$b(fun_app$k(less$a, zero$k), ?v2) ∧ fun_app$b(fun_app$k(less$a, ?v2), one$e))) ⇒ fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v2), ?v1)), fun_app$l(power$(?v2), ?v0)))
tff(axiom279,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'('fun_app$k'('less$a','zero$k'),A__questionmark_v2)
        & 'fun_app$b'('fun_app$k'('less$a',A__questionmark_v2),'one$e') )
     => 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Int (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ ((0 < ?v2) ∧ (?v2 < 1))) ⇒ (fun_app$h(power$a(?v2), ?v1) < fun_app$h(power$a(?v2), ?v0)))
tff(axiom280,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $int] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less(0,A__questionmark_v2)
        & $less(A__questionmark_v2,1) )
     => $less('fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Real (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∧ ((0.0 < ?v2) ∧ (?v2 < 1.0))) ⇒ (fun_app$i(power$b(?v2), ?v1) < fun_app$i(power$b(?v2), ?v0)))
tff(axiom281,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $real] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $less(0.0,A__questionmark_v2)
        & $less(A__questionmark_v2,1.0) )
     => $less('fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$b(fun_app$k(less$a, one$e), ?v0) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ fun_app$b(fun_app$k(less$a, one$e), fun_app$l(power$(?v0), ?v1)))
tff(axiom282,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
     => 'fun_app$b'('fun_app$k'('less$a','one$e'),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ (((1 < ?v0) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ (1 < fun_app$h(power$a(?v0), ?v1)))
tff(axiom283,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( ( $less(1,A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
     => $less(1,'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ (((1.0 < ?v0) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ (1.0 < fun_app$i(power$b(?v0), ?v1)))
tff(axiom284,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( ( $less(1.0,A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
     => $less(1.0,'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (((0 < fun_app$h(of_nat$, ?v0)) ∧ (fun_app$b(?v1, nat$(1)) ∧ ∀ ?v2:Nat$ (((0 < fun_app$h(of_nat$, ?v2)) ∧ fun_app$b(?v1, ?v2)) ⇒ fun_app$b(?v1, nat$((fun_app$h(of_nat$, ?v2) + 1)))))) ⇒ fun_app$b(?v1, ?v0))
tff(axiom285,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        & 'fun_app$b'(A__questionmark_v1,'nat$'(1))
        & ! [A__questionmark_v2: 'Nat$'] :
            ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v2))
              & 'fun_app$b'(A__questionmark_v1,A__questionmark_v2) )
           => 'fun_app$b'(A__questionmark_v1,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))) ) )
     => 'fun_app$b'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom286,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% (fun_app$h(of_nat$, nat$(0)) = 0)
tff(axiom287,axiom,
    'fun_app$h'('of_nat$','nat$'(0)) = 0 ).

%% ∀ ?v0:Nat_rows_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$c(fun_app$d(less$, fun_app$j(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))), fun_app$j(?v0, ?v3)) ∧ (fun_app$h(of_nat$, ?v1) < fun_app$h(of_nat$, ?v2))) ⇒ fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v2)), fun_app$j(?v0, ?v1)))
tff(axiom288,axiom,
    ! [A__questionmark_v0: 'Nat_rows_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1)))),'fun_app$j'(A__questionmark_v0,A__questionmark_v3))
        & $less('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v2)),'fun_app$j'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_rows_fun$ ?v1:Nat$ ?v2:Nat$ (∀ ?v3:Nat$ fun_app$c(fun_app$d(less$, fun_app$j(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))), fun_app$j(?v0, ?v3)) ⇒ (fun_app$c(fun_app$d(less$, fun_app$j(?v0, ?v1)), fun_app$j(?v0, ?v2)) = (fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1))))
tff(axiom289,axiom,
    ! [A__questionmark_v0: 'Nat_rows_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1)))),'fun_app$j'(A__questionmark_v0,A__questionmark_v3))
     => ( 'fun_app$c'('fun_app$d'('less$','fun_app$j'(A__questionmark_v0,A__questionmark_v1)),'fun_app$j'(A__questionmark_v0,A__questionmark_v2))
      <=> $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% (fun_app$h(of_nat$, nat$(1)) = 1)
tff(axiom290,axiom,
    'fun_app$h'('of_nat$','nat$'(1)) = 1 ).

%% ∀ ?v0:Nat$ ?v1:Real (((0 < fun_app$h(of_nat$, ?v0)) ∧ (0.0 < ?v1)) ⇒ ∃ ?v2:Real ((0.0 < ?v2) ∧ (fun_app$i(power$b(?v2), ?v0) = ?v1)))
tff(axiom291,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $real] :
      ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        & $less(0.0,A__questionmark_v1) )
     => ? [A__questionmark_v2: $real] :
          ( $less(0.0,A__questionmark_v2)
          & ( 'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0) = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Real (((0 < fun_app$h(of_nat$, ?v0)) ∧ (0.0 < ?v1)) ⇒ ∃ ?v2:Real (((0.0 < ?v2) ∧ (fun_app$i(power$b(?v2), ?v0) = ?v1)) ∧ ∀ ?v3:Real (((0.0 < ?v3) ∧ (fun_app$i(power$b(?v3), ?v0) = ?v1)) ⇒ (?v3 = ?v2))))
tff(axiom292,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $real] :
      ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v0))
        & $less(0.0,A__questionmark_v1) )
     => ? [A__questionmark_v2: $real] :
          ( $less(0.0,A__questionmark_v2)
          & ( 'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0) = A__questionmark_v1 )
          & ! [A__questionmark_v3: $real] :
              ( ( $less(0.0,A__questionmark_v3)
                & ( 'fun_app$i'('power$b'(A__questionmark_v3),A__questionmark_v0) = A__questionmark_v1 ) )
             => ( A__questionmark_v3 = A__questionmark_v2 ) ) ) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real ((1.0 < ?v0) ⇒ ((powr$(?v0, ?v1) < powr$(?v0, ?v2)) = (?v1 < ?v2)))
tff(axiom293,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( $less(1.0,A__questionmark_v0)
     => ( $less('powr$'(A__questionmark_v0,A__questionmark_v1),'powr$'(A__questionmark_v0,A__questionmark_v2))
      <=> $less(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 < ?v0) ∧ (0.0 < ?v1)) ⇒ ((ln$(?v0) = ln$(?v1)) = (?v0 = ?v1)))
tff(axiom294,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(0.0,A__questionmark_v1) )
     => ( ( 'ln$'(A__questionmark_v0) = 'ln$'(A__questionmark_v1) )
      <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ ((ln$(?v0) = 0.0) = (?v0 = 1.0)))
tff(axiom295,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => ( ( 'ln$'(A__questionmark_v0) = 0.0 )
      <=> ( A__questionmark_v0 = 1.0 ) ) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ ((0.0 < ln$(?v0)) = (1.0 < ?v0)))
tff(axiom296,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => ( $less(0.0,'ln$'(A__questionmark_v0))
      <=> $less(1.0,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ ((ln$(?v0) < 0.0) = (?v0 < 1.0)))
tff(axiom297,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => ( $less('ln$'(A__questionmark_v0),0.0)
      <=> $less(A__questionmark_v0,1.0) ) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 < ?v0) ∧ (0.0 < ?v1)) ⇒ ((ln$(?v0) < ln$(?v1)) = (?v0 < ?v1)))
tff(axiom298,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(0.0,A__questionmark_v1) )
     => ( $less('ln$'(A__questionmark_v0),'ln$'(A__questionmark_v1))
      <=> $less(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Real ?v1:Real ((1.0 < ?v0) ⇒ ((powr$(?v0, ?v1) = 1.0) = (?v1 = 0.0)))
tff(axiom299,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less(1.0,A__questionmark_v0)
     => ( ( 'powr$'(A__questionmark_v0,A__questionmark_v1) = 1.0 )
      <=> ( A__questionmark_v1 = 0.0 ) ) ) ).

%% ∀ ?v0:Real ?v1:Real ((0.0 < powr$(?v0, ?v1)) = ¬(?v0 = 0.0))
tff(axiom300,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less(0.0,'powr$'(A__questionmark_v0,A__questionmark_v1))
    <=> ( A__questionmark_v0 != 0.0 ) ) ).

%% ∀ ?v0:Real ((1.0 < ?v0) ⇒ (0.0 < ln$(?v0)))
tff(axiom301,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(1.0,A__questionmark_v0)
     => $less(0.0,'ln$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ (ln$(?v0) < ?v0))
tff(axiom302,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => $less('ln$'(A__questionmark_v0),A__questionmark_v0) ) ).

%% ∀ ?v0:Real (((0.0 < ?v0) ∧ (?v0 < 1.0)) ⇒ (ln$(?v0) < 0.0))
tff(axiom303,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(A__questionmark_v0,1.0) )
     => $less('ln$'(A__questionmark_v0),0.0) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((0.0 < ?v0) ⇒ (powr$(?v0, fun_app$i(of_nat$a, ?v1)) = fun_app$i(power$b(?v0), ?v1)))
tff(axiom304,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $less(0.0,A__questionmark_v0)
     => ( 'powr$'(A__questionmark_v0,'fun_app$i'('of_nat$a',A__questionmark_v1)) = 'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Real (((0.0 < ln$(?v0)) ∧ (0.0 < ?v0)) ⇒ (1.0 < ?v0))
tff(axiom305,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( $less(0.0,'ln$'(A__questionmark_v0))
        & $less(0.0,A__questionmark_v0) )
     => $less(1.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((?v0 < 0.0) ∧ ((0.0 < ?v1) ∧ (?v1 < ?v2))) ⇒ (powr$(?v2, ?v0) < powr$(?v1, ?v0)))
tff(axiom306,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $less(A__questionmark_v0,0.0)
        & $less(0.0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less('powr$'(A__questionmark_v2,A__questionmark_v0),'powr$'(A__questionmark_v1,A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((powr$(?v0, ?v1) < powr$(?v0, ?v2)) ∧ (1.0 < ?v0)) ⇒ (?v1 < ?v2))
tff(axiom307,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $less('powr$'(A__questionmark_v0,A__questionmark_v1),'powr$'(A__questionmark_v0,A__questionmark_v2))
        & $less(1.0,A__questionmark_v0) )
     => $less(A__questionmark_v1,A__questionmark_v2) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((?v0 < ?v1) ∧ (1.0 < ?v2)) ⇒ (powr$(?v2, ?v0) < powr$(?v2, ?v1)))
tff(axiom308,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $less(1.0,A__questionmark_v2) )
     => $less('powr$'(A__questionmark_v2,A__questionmark_v0),'powr$'(A__questionmark_v2,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real ¬(powr$(?v0, ?v1) < 0.0)
tff(axiom309,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] : ~ $less('powr$'(A__questionmark_v0,A__questionmark_v1),0.0) ).

%% ∀ ?v0:Real ?v1:Real (((1.0 < ?v0) ∧ (0.0 < ?v1)) ⇒ (1.0 < powr$(?v0, ?v1)))
tff(axiom310,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(1.0,A__questionmark_v0)
        & $less(0.0,A__questionmark_v1) )
     => $less(1.0,'powr$'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((0.0 < ?v0) ∧ ¬(?v0 = 1.0)) ⇒ ((powr$(?v0, ?v1) = powr$(?v0, ?v2)) = (?v1 = ?v2)))
tff(axiom311,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & ( A__questionmark_v0 != 1.0 ) )
     => ( ( 'powr$'(A__questionmark_v0,A__questionmark_v1) = 'powr$'(A__questionmark_v0,A__questionmark_v2) )
      <=> ( A__questionmark_v1 = A__questionmark_v2 ) ) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 < ?v0) ∧ (?v1 < 1.0)) ⇒ ∃ ?v2:Nat$ (fun_app$i(power$b(?v1), ?v2) < ?v0))
tff(axiom312,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(A__questionmark_v1,1.0) )
     => ? [A__questionmark_v2: 'Nat$'] : $less('fun_app$i'('power$b'(A__questionmark_v1),A__questionmark_v2),A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ((1.0 < ?v0) ⇒ ∃ ?v2:Nat$ (?v1 < fun_app$i(power$b(?v0), ?v2)))
tff(axiom313,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less(1.0,A__questionmark_v0)
     => ? [A__questionmark_v2: 'Nat$'] : $less(A__questionmark_v1,'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) = (fun_app$c(fun_app$d(less$, ?v1), ?v0) ∨ (?v1 = ?v0)))
tff(axiom314,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
        | ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows_rows_bool_fun_fun$ ?v1:Rows$ ?v2:Rows$ ((∀ ?v3:Rows$ ?v4:Rows$ (fun_app$c(fun_app$d(less$, ?v4), ?v3) ⇒ fun_app$c(fun_app$d(?v0, ?v3), ?v4)) ∧ (∀ ?v3:Rows$ fun_app$c(fun_app$d(?v0, ?v3), ?v3) ∧ ∀ ?v3:Rows$ ?v4:Rows$ (fun_app$c(fun_app$d(?v0, ?v4), ?v3) ⇒ fun_app$c(fun_app$d(?v0, ?v3), ?v4)))) ⇒ fun_app$c(fun_app$d(?v0, ?v1), ?v2))
tff(axiom315,axiom,
    ! [A__questionmark_v0: 'Rows_rows_bool_fun_fun$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( ! [A__questionmark_v3: 'Rows$',A__questionmark_v4: 'Rows$'] :
            ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$c'('fun_app$d'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: 'Rows$'] : 'fun_app$c'('fun_app$d'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: 'Rows$',A__questionmark_v4: 'Rows$'] :
            ( 'fun_app$c'('fun_app$d'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$c'('fun_app$d'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$c'('fun_app$d'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Rows$ ((fun_app$c(fun_app$d(less$, ?v0), ?v1) ∧ (?v0 = ?v2)) ⇒ fun_app$c(fun_app$d(less$, ?v2), ?v1))
tff(axiom316,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v0 = A__questionmark_v2 ) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Rows$ (((?v0 = ?v1) ∧ fun_app$c(fun_app$d(less$, ?v2), ?v1)) ⇒ fun_app$c(fun_app$d(less$, ?v2), ?v0))
tff(axiom317,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v1) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ (¬fun_app$c(fun_app$d(less$, ?v1), ?v0) = true))
tff(axiom318,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
      <=> $true ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ ((?v0 = ?v1) = false))
tff(axiom319,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v0 = A__questionmark_v1 )
      <=> $false ) ) ).

%% ∀ ?v0:Rows_bool_fun$ (∃ ?v1:Rows$ fun_app$c(?v0, ?v1) = ∃ ?v1:Rows$ (fun_app$c(?v0, ?v1) ∧ ∀ ?v2:Rows$ (fun_app$c(fun_app$d(less$, ?v1), ?v2) ⇒ ¬fun_app$c(?v0, ?v2))))
tff(axiom320,axiom,
    ! [A__questionmark_v0: 'Rows_bool_fun$'] :
      ( ? [A__questionmark_v1: 'Rows$'] : 'fun_app$c'(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v1: 'Rows$'] :
          ( 'fun_app$c'(A__questionmark_v0,A__questionmark_v1)
          & ! [A__questionmark_v2: 'Rows$'] :
              ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v2)
             => ~ 'fun_app$c'(A__questionmark_v0,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ ((?v1 = ?v0) = false))
tff(axiom321,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( ( A__questionmark_v1 = A__questionmark_v0 )
      <=> $false ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (((fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ false) ∧ (((?v1 = ?v0) ⇒ false) ∧ (fun_app$c(fun_app$d(less$, ?v1), ?v0) ⇒ false))) ⇒ false)
tff(axiom322,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( ( A__questionmark_v1 = A__questionmark_v0 )
         => $false )
        & ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Bool (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ ((fun_app$c(fun_app$d(less$, ?v1), ?v0) ⇒ ?v2) = true))
tff(axiom323,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: tlbool] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
         => ( A__questionmark_v2 = tltrue ) )
      <=> $true ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ (¬fun_app$c(fun_app$d(less$, ?v1), ?v0) = (?v0 = ?v1)))
tff(axiom324,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
      <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ ¬fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom325,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ ¬(?v1 = ?v0))
tff(axiom326,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( A__questionmark_v1 != A__questionmark_v0 ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ∨ ((?v1 = ?v0) ∨ fun_app$c(fun_app$d(less$, ?v1), ?v0)))
tff(axiom327,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
      | ( A__questionmark_v1 = A__questionmark_v0 )
      | 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ¬fun_app$c(fun_app$d(less$, ?v0), ?v0)
tff(axiom328,axiom,
    ! [A__questionmark_v0: 'Rows$'] : ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Rows_bool_fun$ ?v1:Rows$ (∀ ?v2:Rows$ (∀ ?v3:Rows$ (fun_app$c(fun_app$d(less$, ?v2), ?v3) ⇒ fun_app$c(?v0, ?v3)) ⇒ fun_app$c(?v0, ?v2)) ⇒ fun_app$c(?v0, ?v1))
tff(axiom329,axiom,
    ! [A__questionmark_v0: 'Rows_bool_fun$',A__questionmark_v1: 'Rows$'] :
      ( ! [A__questionmark_v2: 'Rows$'] :
          ( ! [A__questionmark_v3: 'Rows$'] :
              ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v3)
             => 'fun_app$c'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$c'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$c'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Rows$ ((fun_app$c(fun_app$d(less$, ?v0), ?v1) ∧ fun_app$c(fun_app$d(less$, ?v2), ?v0)) ⇒ fun_app$c(fun_app$d(less$, ?v2), ?v1))
tff(axiom330,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ((fun_app$c(fun_app$d(less$, ?v0), ?v1) ∧ fun_app$c(fun_app$d(less$, ?v1), ?v0)) ⇒ false)
tff(axiom331,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ((fun_app$c(fun_app$d(less$, ?v0), ?v1) ∧ (¬false ⇒ fun_app$c(fun_app$d(less$, ?v1), ?v0))) ⇒ false)
tff(axiom332,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) )
     => $false ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬(?v0 = ?v1) = (fun_app$c(fun_app$d(less$, ?v1), ?v0) ∨ fun_app$c(fun_app$d(less$, ?v0), ?v1)))
tff(axiom333,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( A__questionmark_v0 != A__questionmark_v1 )
    <=> ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
        | 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ((¬(?v0 = ?v1) ∧ ((fun_app$c(fun_app$d(less$, ?v1), ?v0) ⇒ false) ∧ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ false))) ⇒ false)
tff(axiom334,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0)
         => $false )
        & ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v0) = false)
tff(axiom335,axiom,
    ! [A__questionmark_v0: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v0)
    <=> $false ) ).

%% ∀ ?v0:Int ((?v0 < ?v0) = false)
tff(axiom336,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v0)
    <=> $false ) ).

%% ∀ ?v0:Real ((?v0 < ?v0) = false)
tff(axiom337,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(A__questionmark_v0,A__questionmark_v0)
    <=> $false ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((0.0 < ?v0) ⇒ ∃ ?v2:Real ((0.0 < ?v2) ∧ (fun_app$i(power$b(?v2), nat$((fun_app$h(of_nat$, ?v1) + 1))) = ?v0)))
tff(axiom338,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $less(0.0,A__questionmark_v0)
     => ? [A__questionmark_v2: $real] :
          ( $less(0.0,A__questionmark_v2)
          & ( 'fun_app$i'('power$b'(A__questionmark_v2),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1))) = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom339,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Bool ?v1:Nat$ ?v2:Nat$ (fun_app$h(of_nat$, (if ?v0 ?v1 else ?v2)) = (if ?v0 fun_app$h(of_nat$, ?v1) else fun_app$h(of_nat$, ?v2)))
tff(axiom340,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ( A__questionmark_v0 = tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ) )
      & ( ( A__questionmark_v0 != tltrue )
       => ( ( ( A__questionmark_v0 = tltrue )
           => ( 'fun_app$h'('of_nat$',A__questionmark_v2) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
          & ( ( A__questionmark_v0 != tltrue )
           => ( 'fun_app$h'('of_nat$',A__questionmark_v2) = 'fun_app$h'('of_nat$',A__questionmark_v2) ) ) ) ) ) ).

%% ∀ ?v0:Nat$ ((((fun_app$h(of_nat$, ?v0) = 0) ⇒ false) ∧ ∀ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)) ⇒ false)) ⇒ false)
tff(axiom341,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( ( ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int (((0 + 1) < fun_app$h(of_nat$, nat$(?v0))) = (1 < ?v0))
tff(axiom342,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($sum(0,1),'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)))
    <=> $less(1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int (((?v0 < 0) ∧ ∀ ?v1:Nat$ (((?v0 = -fun_app$h(of_nat$, ?v1)) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom343,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $less(A__questionmark_v0,0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$',A__questionmark_v1)) )
              & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less$a, ?v0), ?v1) ∧ (fun_app$b(fun_app$k(less_eq$, zero$k), ?v0) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ fun_app$b(fun_app$k(less$a, fun_app$l(power$(?v0), ?v2)), fun_app$l(power$(?v1), ?v2)))
tff(axiom344,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => 'fun_app$b'('fun_app$k'('less$a','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Nat$ (((?v0 < ?v1) ∧ ((0 ≤ ?v0) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ (fun_app$h(power$a(?v0), ?v2) < fun_app$h(power$a(?v1), ?v2)))
tff(axiom345,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Nat$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(0,A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $less('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2),'fun_app$h'('power$a'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Nat$ (((?v0 < ?v1) ∧ ((0.0 ≤ ?v0) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ (fun_app$i(power$b(?v0), ?v2) < fun_app$i(power$b(?v1), ?v2)))
tff(axiom346,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: 'Nat$'] :
      ( ( $less(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(0.0,A__questionmark_v0)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $less('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2),'fun_app$i'('power$b'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 = -?v1) = (?v0 = ?v1))
tff(axiom347,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $uminus(A__questionmark_v0) = $uminus(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int (--?v0 = ?v0)
tff(axiom348,axiom,
    ! [A__questionmark_v0: $int] : ( $uminus($uminus(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$h(of_nat$, ?v0))
tff(axiom349,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$h(of_nat$, ?v0))
tff(axiom350,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) ≤ (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom351,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 ≤ -?v1) = (?v1 ≤ ?v0))
tff(axiom352,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ((-?v0 ≤ -?v1) = (?v1 ≤ ?v0))
tff(axiom353,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,A__questionmark_v0) ) ).

%% (0.0 = 0.0)
tff(axiom354,axiom,
    0.0 = 0.0 ).

%% (uminus$(zero$) = zero$)
tff(axiom355,axiom,
    'uminus$'('zero$') = 'zero$' ).

%% (uminus$a(zero$a) = zero$a)
tff(axiom356,axiom,
    'uminus$a'('zero$a') = 'zero$a' ).

%% (0 = 0)
tff(axiom357,axiom,
    0 = 0 ).

%% ∀ ?v0:Real ((0.0 = -?v0) = (0.0 = ?v0))
tff(axiom358,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( 0.0 = $uminus(A__questionmark_v0) )
    <=> ( 0.0 = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Rows$ ((zero$ = uminus$(?v0)) = (zero$ = ?v0))
tff(axiom359,axiom,
    ! [A__questionmark_v0: 'Rows$'] :
      ( ( 'zero$' = 'uminus$'(A__questionmark_v0) )
    <=> ( 'zero$' = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Cols$ ((zero$a = uminus$a(?v0)) = (zero$a = ?v0))
tff(axiom360,axiom,
    ! [A__questionmark_v0: 'Cols$'] :
      ( ( 'zero$a' = 'uminus$a'(A__questionmark_v0) )
    <=> ( 'zero$a' = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ((0 = -?v0) = (0 = ?v0))
tff(axiom361,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 0 = $uminus(A__questionmark_v0) )
    <=> ( 0 = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Real ((-?v0 = 0.0) = (?v0 = 0.0))
tff(axiom362,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( $uminus(A__questionmark_v0) = 0.0 )
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Rows$ ((uminus$(?v0) = zero$) = (?v0 = zero$))
tff(axiom363,axiom,
    ! [A__questionmark_v0: 'Rows$'] :
      ( ( 'uminus$'(A__questionmark_v0) = 'zero$' )
    <=> ( A__questionmark_v0 = 'zero$' ) ) ).

%% ∀ ?v0:Cols$ ((uminus$a(?v0) = zero$a) = (?v0 = zero$a))
tff(axiom364,axiom,
    ! [A__questionmark_v0: 'Cols$'] :
      ( ( 'uminus$a'(A__questionmark_v0) = 'zero$a' )
    <=> ( A__questionmark_v0 = 'zero$a' ) ) ).

%% ∀ ?v0:Int ((-?v0 = 0) = (?v0 = 0))
tff(axiom365,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $uminus(A__questionmark_v0) = 0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Real ((?v0 = -?v0) = (?v0 = 0.0))
tff(axiom366,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v0) )
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Int ((?v0 = -?v0) = (?v0 = 0))
tff(axiom367,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v0) )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Real ((-?v0 = ?v0) = (?v0 = 0.0))
tff(axiom368,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Int ((-?v0 = ?v0) = (?v0 = 0))
tff(axiom369,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v0 )
    <=> ( A__questionmark_v0 = 0 ) ) ).

%% ∀ ?v0:Real ?v1:Real ((-?v0 < -?v1) = (?v1 < ?v0))
tff(axiom370,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 < -?v1) = (?v1 < ?v0))
tff(axiom371,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($uminus(A__questionmark_v0),$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom372,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$i(of_nat$a, ?v0) ≤ fun_app$i(of_nat$a, ?v1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom373,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('of_nat$a',A__questionmark_v1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real ((powr$(?v0, ?v1) ≤ 0.0) = (?v0 = 0.0))
tff(axiom374,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq('powr$'(A__questionmark_v0,A__questionmark_v1),0.0)
    <=> ( A__questionmark_v0 = 0.0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (-fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1))
tff(axiom375,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $lesseq($uminus('fun_app$h'('of_nat$',A__questionmark_v0)),'fun_app$h'('of_nat$',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v0))
tff(axiom376,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((0 ≤ -?v0) = (?v0 ≤ 0))
tff(axiom377,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Real ((0.0 ≤ -?v0) = (?v0 ≤ 0.0))
tff(axiom378,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq(0.0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0.0) ) ).

%% ∀ ?v0:Int ((-?v0 ≤ 0) = (0 ≤ ?v0))
tff(axiom379,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq($uminus(A__questionmark_v0),0)
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ((-?v0 ≤ 0.0) = (0.0 ≤ ?v0))
tff(axiom380,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq($uminus(A__questionmark_v0),0.0)
    <=> $lesseq(0.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((?v0 ≤ -?v0) = (?v0 ≤ 0))
tff(axiom381,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Real ((?v0 ≤ -?v0) = (?v0 ≤ 0.0))
tff(axiom382,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $lesseq(A__questionmark_v0,0.0) ) ).

%% ∀ ?v0:Int ((-?v0 ≤ ?v0) = (0 ≤ ?v0))
tff(axiom383,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $lesseq(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ((-?v0 ≤ ?v0) = (0.0 ≤ ?v0))
tff(axiom384,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $lesseq(0.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ((?v0 < -?v0) = (?v0 < 0.0))
tff(axiom385,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0.0) ) ).

%% ∀ ?v0:Int ((?v0 < -?v0) = (?v0 < 0))
tff(axiom386,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Real ((-?v0 < ?v0) = (0.0 < ?v0))
tff(axiom387,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $less(0.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((-?v0 < ?v0) = (0 < ?v0))
tff(axiom388,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v0)
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ((0.0 < -?v0) = (?v0 < 0.0))
tff(axiom389,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0.0) ) ).

%% ∀ ?v0:Int ((0 < -?v0) = (?v0 < 0))
tff(axiom390,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,$uminus(A__questionmark_v0))
    <=> $less(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Real ((-?v0 < 0.0) = (0.0 < ?v0))
tff(axiom391,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less($uminus(A__questionmark_v0),0.0)
    <=> $less(0.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((-?v0 < 0) = (0 < ?v0))
tff(axiom392,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less($uminus(A__questionmark_v0),0)
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ((?v0 ≤ 0) ⇒ (fun_app$h(of_nat$, nat$(?v0)) = 0))
tff(axiom393,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(A__questionmark_v0,0)
     => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 0 ) ) ).

%% ∀ ?v0:Int ((fun_app$h(of_nat$, nat$(?v0)) = 0) = (?v0 ≤ 0))
tff(axiom394,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 0 )
    <=> $lesseq(A__questionmark_v0,0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((-fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) = 0) ∧ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom395,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $uminus('fun_app$h'('of_nat$',A__questionmark_v0)) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
        & ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 < ?v0) ∧ (0.0 < ?v1)) ⇒ ((ln$(?v0) ≤ ln$(?v1)) = (?v0 ≤ ?v1)))
tff(axiom396,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(0.0,A__questionmark_v1) )
     => ( $lesseq('ln$'(A__questionmark_v0),'ln$'(A__questionmark_v1))
      <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Real ((0.0 ≤ ?v0) ⇒ (powr$(?v0, 1.0) = ?v0))
tff(axiom397,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq(0.0,A__questionmark_v0)
     => ( 'powr$'(A__questionmark_v0,1.0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Real ((powr$(?v0, 1.0) = ?v0) = (0.0 ≤ ?v0))
tff(axiom398,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( 'powr$'(A__questionmark_v0,1.0) = A__questionmark_v0 )
    <=> $lesseq(0.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real ((1.0 < ?v0) ⇒ ((powr$(?v0, ?v1) ≤ powr$(?v0, ?v2)) = (?v1 ≤ ?v2)))
tff(axiom399,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( $less(1.0,A__questionmark_v0)
     => ( $lesseq('powr$'(A__questionmark_v0,A__questionmark_v1),'powr$'(A__questionmark_v0,A__questionmark_v2))
      <=> $lesseq(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int (fun_app$h(of_nat$, nat$(?v0)) = (if (0 ≤ ?v0) ?v0 else 0))
tff(axiom400,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = A__questionmark_v0 ) )
      & ( ~ $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 0 ) ) ) ).

%% (dbl_inc$(-1.0) = -1.0)
tff(axiom401,axiom,
    'dbl_inc$'($uminus(1.0)) = $uminus(1.0) ).

%% (dbl_inc$a(-1) = -1)
tff(axiom402,axiom,
    'dbl_inc$a'($uminus(1)) = $uminus(1) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less$a, one$e), ?v0) ⇒ (fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))))
tff(axiom403,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
     => ( 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ ((1 < ?v0) ⇒ ((fun_app$h(power$a(?v0), ?v1) ≤ fun_app$h(power$a(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))))
tff(axiom404,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1,A__questionmark_v0)
     => ( $lesseq('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ ((1.0 < ?v0) ⇒ ((fun_app$i(power$b(?v0), ?v1) ≤ fun_app$i(power$b(?v0), ?v2)) = (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))))
tff(axiom405,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $less(1.0,A__questionmark_v0)
     => ( $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ 0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom406,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),0)
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$i(of_nat$a, ?v0) ≤ 0.0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom407,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$i'('of_nat$a',A__questionmark_v0),0.0)
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less_eq$, fun_app$l(of_nat$b, ?v0)), fun_app$l(power$(fun_app$l(of_nat$b, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom408,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('of_nat$b',A__questionmark_v0)),'fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v1)),A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(power$a(fun_app$h(of_nat$, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom409,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v1)),A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(of_nat$a, ?v0) ≤ fun_app$i(power$b(fun_app$i(of_nat$a, ?v1)), ?v2)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, fun_app$l(power$(?v1), ?v2))))
tff(axiom410,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $lesseq('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v1)),A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(fun_app$l(of_nat$b, ?v0)), ?v1)), fun_app$l(of_nat$b, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom411,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'('fun_app$l'('of_nat$b',A__questionmark_v0)),A__questionmark_v1)),'fun_app$l'('of_nat$b',A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$h(power$a(fun_app$h(of_nat$, ?v0)), ?v1) ≤ fun_app$h(of_nat$, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom412,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $lesseq('fun_app$h'('power$a'('fun_app$h'('of_nat$',A__questionmark_v0)),A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$i(power$b(fun_app$i(of_nat$a, ?v0)), ?v1) ≤ fun_app$i(of_nat$a, ?v2)) = (fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1)) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom413,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( $lesseq('fun_app$i'('power$b'('fun_app$i'('of_nat$a',A__questionmark_v0)),A__questionmark_v1),'fun_app$i'('of_nat$a',A__questionmark_v2))
    <=> $lesseq('fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% (fun_app$h(of_nat$, nat$(1)) = (0 + 1))
tff(axiom414,axiom,
    'fun_app$h'('of_nat$','nat$'(1)) = $sum(0,1) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ ((ln$(?v0) ≤ 0.0) = (?v0 ≤ 1.0)))
tff(axiom415,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => ( $lesseq('ln$'(A__questionmark_v0),0.0)
      <=> $lesseq(A__questionmark_v0,1.0) ) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ ((0.0 ≤ ln$(?v0)) = (1.0 ≤ ?v0)))
tff(axiom416,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => ( $lesseq(0.0,'ln$'(A__questionmark_v0))
      <=> $lesseq(1.0,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((fun_app$h(of_nat$, nat$(?v0)) < fun_app$h(of_nat$, nat$(?v1))) = ((0 < ?v1) ∧ (?v0 < ?v1)))
tff(axiom417,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)))
    <=> ( $less(0,A__questionmark_v1)
        & $less(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (-fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v0) + 1))) < fun_app$h(of_nat$, ?v1))
tff(axiom418,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : $less($uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1)))),'fun_app$h'('of_nat$',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ (fun_app$h(of_nat$, nat$(-fun_app$h(of_nat$, ?v0))) = 0)
tff(axiom419,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$h'('of_nat$','nat$'($uminus('fun_app$h'('of_nat$',A__questionmark_v0)))) = 0 ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less$a, zero$k), ?v0) ∧ fun_app$b(fun_app$k(less$a, ?v0), one$e)) ⇒ (fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) ≤ fun_app$h(of_nat$, ?v1))))
tff(axiom420,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','zero$k'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less$a',A__questionmark_v0),'one$e') )
     => ( 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ (((0 < ?v0) ∧ (?v0 < 1)) ⇒ ((fun_app$h(power$a(?v0), ?v1) ≤ fun_app$h(power$a(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) ≤ fun_app$h(of_nat$, ?v1))))
tff(axiom421,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(0,A__questionmark_v0)
        & $less(A__questionmark_v0,1) )
     => ( $lesseq('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ (((0.0 < ?v0) ∧ (?v0 < 1.0)) ⇒ ((fun_app$i(power$b(?v0), ?v1) ≤ fun_app$i(power$b(?v0), ?v2)) = (fun_app$h(of_nat$, ?v2) ≤ fun_app$h(of_nat$, ?v1))))
tff(axiom422,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(0.0,A__questionmark_v0)
        & $less(A__questionmark_v0,1.0) )
     => ( $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less_eq$, zero$k), ?v0) ∧ (fun_app$b(fun_app$k(less_eq$, zero$k), ?v1) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ (fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v0), ?v2)), fun_app$l(power$(?v1), ?v2)) = fun_app$b(fun_app$k(less_eq$, ?v0), ?v1)))
tff(axiom423,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v1)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => ( 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2))
      <=> 'fun_app$b'('fun_app$k'('less_eq$',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Nat$ (((0 ≤ ?v0) ∧ ((0 ≤ ?v1) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ ((fun_app$h(power$a(?v0), ?v2) ≤ fun_app$h(power$a(?v1), ?v2)) = (?v0 ≤ ?v1)))
tff(axiom424,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq(0,A__questionmark_v0)
        & $lesseq(0,A__questionmark_v1)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => ( $lesseq('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2),'fun_app$h'('power$a'(A__questionmark_v1),A__questionmark_v2))
      <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Nat$ (((0.0 ≤ ?v0) ∧ ((0.0 ≤ ?v1) ∧ (0 < fun_app$h(of_nat$, ?v2)))) ⇒ ((fun_app$i(power$b(?v0), ?v2) ≤ fun_app$i(power$b(?v1), ?v2)) = (?v0 ≤ ?v1)))
tff(axiom425,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq(0.0,A__questionmark_v0)
        & $lesseq(0.0,A__questionmark_v1)
        & $less(0,'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => ( $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2),'fun_app$i'('power$b'(A__questionmark_v1),A__questionmark_v2))
      <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ((0 < fun_app$h(of_nat$, nat$(?v0))) = (0 < ?v0))
tff(axiom426,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(0,'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)))
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 ≤ ?v0) ⇒ ((fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, nat$(?v0))) = (fun_app$h(of_nat$, ?v1) ≤ ?v0)))
tff(axiom427,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0,A__questionmark_v0)
     => ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)))
      <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Real ((1.0 ≤ ?v0) ⇒ (0.0 ≤ ln$(?v0)))
tff(axiom428,axiom,
    ! [A__questionmark_v0: $real] :
      ( $lesseq(1.0,A__questionmark_v0)
     => $lesseq(0.0,'ln$'(A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom429,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ⇒ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ∨ (?v1 = ?v0)))
tff(axiom430,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        | ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ⇒ fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom431,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) = (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∧ ¬fun_app$c(fun_app$d(less_eq$a, ?v1), ?v0)))
tff(axiom432,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
        & ~ 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∨ fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom433,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
      | 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Rows$ ((fun_app$c(fun_app$d(less$, ?v0), ?v1) ∧ fun_app$c(fun_app$d(less_eq$a, ?v2), ?v0)) ⇒ fun_app$c(fun_app$d(less$, ?v2), ?v1))
tff(axiom434,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ?v2:Rows$ ((fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∧ fun_app$c(fun_app$d(less$, ?v2), ?v0)) ⇒ fun_app$c(fun_app$d(less$, ?v2), ?v1))
tff(axiom435,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$',A__questionmark_v2: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ⇒ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) = (?v1 = ?v0)))
tff(axiom436,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
     => ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) = (?v1 = ?v0)))
tff(axiom437,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ((¬(?v0 = ?v1) ∧ fun_app$c(fun_app$d(less_eq$a, ?v1), ?v0)) ⇒ fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom438,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( ( A__questionmark_v0 != A__questionmark_v1 )
        & 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v1),A__questionmark_v0) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ ((fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∧ ¬(?v1 = ?v0)) ⇒ fun_app$c(fun_app$d(less$, ?v0), ?v1))
tff(axiom439,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v1 != A__questionmark_v0 ) )
     => 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1))
tff(axiom440,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) = fun_app$c(fun_app$d(less_eq$a, ?v1), ?v0))
tff(axiom441,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
    <=> 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) = (¬fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∨ (?v1 = ?v0)))
tff(axiom442,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
    <=> ( ~ 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
        | ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less$, ?v0), ?v1) = (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ∧ ¬(?v1 = ?v0)))
tff(axiom443,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v1 != A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) = (fun_app$c(fun_app$d(less$, ?v0), ?v1) ∨ (?v1 = ?v0)))
tff(axiom444,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
        | ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) = fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom445,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
    <=> 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less$, ?v0), ?v1) ⇒ fun_app$c(fun_app$d(less_eq$a, ?v1), ?v0))
tff(axiom446,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) ⇒ ¬fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom447,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
     => ~ 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Rows$ ?v1:Rows$ (¬fun_app$c(fun_app$d(less_eq$a, ?v0), ?v1) = fun_app$c(fun_app$d(less$, ?v1), ?v0))
tff(axiom448,axiom,
    ! [A__questionmark_v0: 'Rows$',A__questionmark_v1: 'Rows$'] :
      ( ~ 'fun_app$c'('fun_app$d'('less_eq$a',A__questionmark_v0),A__questionmark_v1)
    <=> 'fun_app$c'('fun_app$d'('less$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int (¬(?v0 ≤ ?v1) = (?v1 < ?v0))
tff(axiom449,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ~ $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real (¬(?v0 ≤ ?v1) = (?v1 < ?v0))
tff(axiom450,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ~ $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> $less(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ((?v0 < ?v1) ⇒ (-?v1 < -?v0))
tff(axiom451,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < ?v1) ⇒ (-?v1 < -?v0))
tff(axiom452,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,A__questionmark_v1)
     => $less($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ((?v0 ≤ ?v1) = ((?v0 < ?v1) ∨ (?v0 = ?v1)))
tff(axiom453,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( $less(A__questionmark_v0,A__questionmark_v1)
        | ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Real ?v1:Real (((1.0 ≤ ?v0) ∧ (0.0 ≤ ?v1)) ⇒ (1.0 ≤ powr$(?v0, ?v1)))
tff(axiom454,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $lesseq(1.0,A__questionmark_v0)
        & $lesseq(0.0,A__questionmark_v1) )
     => $lesseq(1.0,'powr$'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real ?v3:Real (((0.0 ≤ ?v0) ∧ ((?v0 ≤ ?v1) ∧ ((1.0 ≤ ?v2) ∧ (?v2 ≤ ?v3)))) ⇒ (powr$(?v2, ?v0) ≤ powr$(?v3, ?v1)))
tff(axiom455,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real,A__questionmark_v3: $real] :
      ( ( $lesseq(0.0,A__questionmark_v0)
        & $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(1.0,A__questionmark_v2)
        & $lesseq(A__questionmark_v2,A__questionmark_v3) )
     => $lesseq('powr$'(A__questionmark_v2,A__questionmark_v0),'powr$'(A__questionmark_v3,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real (0.0 ≤ powr$(?v0, ?v1))
tff(axiom456,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] : $lesseq(0.0,'powr$'(A__questionmark_v0,A__questionmark_v1)) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((0.0 ≤ ?v0) ∧ ((0.0 ≤ ?v1) ∧ (?v1 ≤ ?v2))) ⇒ (powr$(?v1, ?v0) ≤ powr$(?v2, ?v0)))
tff(axiom457,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $lesseq(0.0,A__questionmark_v0)
        & $lesseq(0.0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq('powr$'(A__questionmark_v1,A__questionmark_v0),'powr$'(A__questionmark_v2,A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((?v0 ≤ ?v1) ∧ (1.0 ≤ ?v2)) ⇒ (powr$(?v2, ?v0) ≤ powr$(?v2, ?v1)))
tff(axiom458,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(1.0,A__questionmark_v2) )
     => $lesseq('powr$'(A__questionmark_v2,A__questionmark_v0),'powr$'(A__questionmark_v2,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real (((0.0 ≤ ?v0) ∧ ((0.0 ≤ ?v1) ∧ (?v1 ≤ 1.0))) ⇒ (powr$(?v1, ?v0) ≤ 1.0))
tff(axiom459,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( ( $lesseq(0.0,A__questionmark_v0)
        & $lesseq(0.0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,1.0) )
     => $lesseq('powr$'(A__questionmark_v1,A__questionmark_v0),1.0) ) ).

%% ∀ ?v0:Int ?v1:Int (((0 ≤ ?v0) ∧ (0 ≤ ?v1)) ⇒ ((fun_app$h(of_nat$, nat$(?v0)) = fun_app$h(of_nat$, nat$(?v1))) = (?v0 = ?v1)))
tff(axiom460,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
        & $lesseq(0,A__questionmark_v1) )
     => ( ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)) )
      <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int (((0 < ?v0) ∨ (0 ≤ ?v1)) ⇒ ((fun_app$h(of_nat$, nat$(?v0)) ≤ fun_app$h(of_nat$, nat$(?v1))) = (?v0 ≤ ?v1)))
tff(axiom461,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $less(0,A__questionmark_v0)
        | $lesseq(0,A__questionmark_v1) )
     => ( $lesseq('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)))
      <=> $lesseq(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 ≤ ?v0) ⇒ (fun_app$h(of_nat$, nat$(fun_app$h(power$a(?v0), ?v1))) = fun_app$h(of_nat$, fun_app$l(power$(nat$(?v0)), ?v1))))
tff(axiom462,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0,A__questionmark_v0)
     => ( 'fun_app$h'('of_nat$','nat$'('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1))) = 'fun_app$h'('of_nat$','fun_app$l'('power$'('nat$'(A__questionmark_v0)),A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∀ ?v1:Nat$ fun_app$b(?v0, ?v1) = ∀ ?v1:Int ((0 ≤ ?v1) ⇒ fun_app$b(?v0, nat$(?v1))))
tff(axiom463,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v1: 'Nat$'] : 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v1: $int] :
          ( $lesseq(0,A__questionmark_v1)
         => 'fun_app$b'(A__questionmark_v0,'nat$'(A__questionmark_v1)) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ (∃ ?v1:Nat$ fun_app$b(?v0, ?v1) = ∃ ?v1:Int ((0 ≤ ?v1) ∧ fun_app$b(?v0, nat$(?v1))))
tff(axiom464,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v1: 'Nat$'] : 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
    <=> ? [A__questionmark_v1: $int] :
          ( $lesseq(0,A__questionmark_v1)
          & 'fun_app$b'(A__questionmark_v0,'nat$'(A__questionmark_v1)) ) ) ).

%% (-1 ≤ 1)
tff(axiom465,axiom,
    $lesseq($uminus(1),1) ).

%% (-1.0 ≤ 1.0)
tff(axiom466,axiom,
    $lesseq($uminus(1.0),1.0) ).

%% ¬(1 ≤ -1)
tff(axiom467,axiom,
    ~ $lesseq(1,$uminus(1)) ).

%% ¬(1.0 ≤ -1.0)
tff(axiom468,axiom,
    ~ $lesseq(1.0,$uminus(1.0)) ).

%% (-1 ≤ 0)
tff(axiom469,axiom,
    $lesseq($uminus(1),0) ).

%% (-1.0 ≤ 0.0)
tff(axiom470,axiom,
    $lesseq($uminus(1.0),0.0) ).

%% ¬(0 ≤ -1)
tff(axiom471,axiom,
    ~ $lesseq(0,$uminus(1)) ).

%% ¬(0.0 ≤ -1.0)
tff(axiom472,axiom,
    ~ $lesseq(0.0,$uminus(1.0)) ).

%% ∀ ?v0:Nat$ ?v1:Int ((fun_app$h(of_nat$, ?v0) = ?v1) = ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, nat$(?v1))) ∧ (0 ≤ ?v1)))
tff(axiom473,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $int] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = A__questionmark_v1 )
    <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)) )
        & $lesseq(0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ((0 ≤ ?v0) ⇒ (fun_app$h(of_nat$, nat$(?v0)) = ?v0))
tff(axiom474,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,A__questionmark_v0)
     => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ fun_app$b(fun_app$k(less_eq$, one$e), ?v2)) ⇒ fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v2), ?v0)), fun_app$l(power$(?v2), ?v1)))
tff(axiom475,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'('fun_app$k'('less_eq$','one$e'),A__questionmark_v2) )
     => 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v0)),'fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Int (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (1 ≤ ?v2)) ⇒ (fun_app$h(power$a(?v2), ?v0) ≤ fun_app$h(power$a(?v2), ?v1)))
tff(axiom476,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $int] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq(1,A__questionmark_v2) )
     => $lesseq('fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v0),'fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Real (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (1.0 ≤ ?v2)) ⇒ (fun_app$i(power$b(?v2), ?v0) ≤ fun_app$i(power$b(?v2), ?v1)))
tff(axiom477,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $real] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq(1.0,A__questionmark_v2) )
     => $lesseq('fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0),'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ -fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) = 0) ∧ (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom478,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),$uminus('fun_app$h'('of_nat$',A__questionmark_v1)))
    <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 )
        & ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ).

%% ∀ ?v0:Int (((?v0 ≤ 0) ∧ ∀ ?v1:Nat$ ((?v0 = -fun_app$h(of_nat$, ?v1)) ⇒ false)) ⇒ false)
tff(axiom479,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(A__questionmark_v0,0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ (-fun_app$h(of_nat$, ?v0) ≤ 0)
tff(axiom480,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq($uminus('fun_app$h'('of_nat$',A__questionmark_v0)),0) ).

%% ∀ ?v0:Real ?v1:Real ((-?v0 < ?v1) = (-?v1 < ?v0))
tff(axiom481,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $less($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 < ?v1) = (-?v1 < ?v0))
tff(axiom482,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $less($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ((?v0 < -?v1) = (?v1 < -?v0))
tff(axiom483,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 < -?v1) = (?v1 < -?v0))
tff(axiom484,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $less(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ¬(1.0 = -1.0)
tff(axiom485,axiom,
    1.0 != $uminus(1.0) ).

%% ¬(1 = -1)
tff(axiom486,axiom,
    1 != $uminus(1) ).

%% ∀ ?v0:Rows$ fun_app$c(fun_app$d(less_eq$a, zero$), ?v0)
tff(axiom487,axiom,
    ! [A__questionmark_v0: 'Rows$'] : 'fun_app$c'('fun_app$d'('less_eq$a','zero$'),A__questionmark_v0) ).

%% ∀ ?v0:Cols$ less_eq$b(zero$a, ?v0)
tff(axiom488,axiom,
    ! [A__questionmark_v0: 'Cols$'] : 'less_eq$b'('zero$a',A__questionmark_v0) ).

%% (0 ≤ 0)
tff(axiom489,axiom,
    $lesseq(0,0) ).

%% (0.0 ≤ 0.0)
tff(axiom490,axiom,
    $lesseq(0.0,0.0) ).

%% (1 ≤ 1)
tff(axiom491,axiom,
    $lesseq(1,1) ).

%% (1.0 ≤ 1.0)
tff(axiom492,axiom,
    $lesseq(1.0,1.0) ).

%% (0 = 0)
tff(axiom493,axiom,
    0 = 0 ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ 0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom494,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),0)
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ 0) ⇒ (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom495,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),0)
     => ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ 0) = (fun_app$h(of_nat$, ?v0) = 0))
tff(axiom496,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),0)
    <=> ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ).

%% ∀ ?v0:Nat$ ((0 ≤ fun_app$h(of_nat$, ?v0)) = true)
tff(axiom497,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq(0,'fun_app$h'('of_nat$',A__questionmark_v0))
    <=> $true ) ).

%% ∀ ?v0:Real ∃ ?v1:Nat$ (?v0 ≤ fun_app$i(of_nat$a, ?v1))
tff(axiom498,axiom,
    ! [A__questionmark_v0: $real] :
    ? [A__questionmark_v1: 'Nat$'] : $lesseq(A__questionmark_v0,'fun_app$i'('of_nat$a',A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom499,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ (fun_app$h(of_nat$, ?v1) + 1)) ∧ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1)) ⇒ false))) ⇒ false)
tff(axiom500,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
        & ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
         => $false )
        & ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) ≤ (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom501,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)) ⇒ ∃ ?v2:Nat$ (fun_app$h(of_nat$, ?v1) = (fun_app$h(of_nat$, ?v2) + 1)))
tff(axiom502,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ? [A__questionmark_v2: 'Nat$'] : ( 'fun_app$h'('of_nat$',A__questionmark_v1) = $sum('fun_app$h'('of_nat$',A__questionmark_v2),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ (fun_app$h(of_nat$, ?v1) + 1)) = ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v0) = (fun_app$h(of_nat$, ?v1) + 1))))
tff(axiom503,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v0) = $sum('fun_app$h'('of_nat$',A__questionmark_v1),1) ) ) ) ).

%% ∀ ?v0:Nat$ ¬((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v0))
tff(axiom504,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v1) + 1) ≤ fun_app$h(of_nat$, ?v0)))
tff(axiom505,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v1),1),'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (∀ ?v3:Nat$ (((fun_app$h(of_nat$, ?v3) + 1) ≤ fun_app$h(of_nat$, ?v2)) ⇒ fun_app$b(?v0, ?v3)) ⇒ fun_app$b(?v0, ?v2)) ⇒ fun_app$b(?v0, ?v1))
tff(axiom506,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ! [A__questionmark_v3: 'Nat$'] :
              ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v3),1),'fun_app$h'('of_nat$',A__questionmark_v2))
             => 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$b'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$b(?v2, ?v0) ∧ ∀ ?v3:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ∧ fun_app$b(?v2, ?v3)) ⇒ fun_app$b(?v2, nat$((fun_app$h(of_nat$, ?v3) + 1)))))) ⇒ fun_app$b(?v2, ?v1))
tff(axiom507,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'(A__questionmark_v2,A__questionmark_v0)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
              & 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) )
           => 'fun_app$b'(A__questionmark_v2,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))) ) )
     => 'fun_app$b'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_bool_fun_fun$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ fun_app$b(fun_app$k(?v2, ?v3), ?v3) ∧ (∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ ((fun_app$b(fun_app$k(?v2, ?v3), ?v4) ∧ fun_app$b(fun_app$k(?v2, ?v4), ?v5)) ⇒ fun_app$b(fun_app$k(?v2, ?v3), ?v5)) ∧ ∀ ?v3:Nat$ fun_app$b(fun_app$k(?v2, ?v3), nat$((fun_app$h(of_nat$, ?v3) + 1)))))) ⇒ fun_app$b(fun_app$k(?v2, ?v0), ?v1))
tff(axiom508,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)
              & 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v4),A__questionmark_v5) )
           => 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5) )
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v3),'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))) )
     => 'fun_app$b'('fun_app$k'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ ((?v0 = -fun_app$h(of_nat$, ?v1)) ⇒ false)) ⇒ false)
tff(axiom509,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ ¬(fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))))
tff(axiom510,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom511,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))))
tff(axiom512,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom513,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ ¬(fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1))) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom514,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & ( 'fun_app$h'('of_nat$',A__questionmark_v0) != 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_nat_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v4)) ⇒ (fun_app$h(of_nat$, fun_app$l(?v0, ?v3)) < fun_app$h(of_nat$, fun_app$l(?v0, ?v4)))) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$h(of_nat$, fun_app$l(?v0, ?v1)) ≤ fun_app$h(of_nat$, fun_app$l(?v0, ?v2))))
tff(axiom515,axiom,
    ! [A__questionmark_v0: 'Nat_nat_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v4))
           => $less('fun_app$h'('of_nat$','fun_app$l'(A__questionmark_v0,A__questionmark_v3)),'fun_app$h'('of_nat$','fun_app$l'(A__questionmark_v0,A__questionmark_v4))) )
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$h'('of_nat$','fun_app$l'(A__questionmark_v0,A__questionmark_v1)),'fun_app$h'('of_nat$','fun_app$l'(A__questionmark_v0,A__questionmark_v2))) ) ).

%% ((0 ≤ 0) = true)
tff(axiom516,axiom,
    ( $lesseq(0,0)
  <=> $true ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (-?v1 ≤ -?v0))
tff(axiom517,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ((?v0 ≤ ?v1) ⇒ (-?v1 ≤ -?v0))
tff(axiom518,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq($uminus(A__questionmark_v1),$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 ≤ ?v1) = (-?v1 ≤ ?v0))
tff(axiom519,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $lesseq($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Real ?v1:Real ((-?v0 ≤ ?v1) = (-?v1 ≤ ?v0))
tff(axiom520,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq($uminus(A__questionmark_v0),A__questionmark_v1)
    <=> $lesseq($uminus(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ -?v1) = (?v1 ≤ -?v0))
tff(axiom521,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ((?v0 ≤ -?v1) = (?v1 ≤ -?v0))
tff(axiom522,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real] :
      ( $lesseq(A__questionmark_v0,$uminus(A__questionmark_v1))
    <=> $lesseq(A__questionmark_v1,$uminus(A__questionmark_v0)) ) ).

%% ∀ ?v0:Int ?v1:Int ((-?v0 = ?v1) = (-?v1 = ?v0))
tff(axiom523,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $uminus(A__questionmark_v0) = A__questionmark_v1 )
    <=> ( $uminus(A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = -?v1) = (?v1 = -?v0))
tff(axiom524,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = $uminus(A__questionmark_v1) )
    <=> ( A__questionmark_v1 = $uminus(A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$h(?v0, ?v3) ≤ fun_app$h(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$h(?v0, ?v1) ≤ fun_app$h(?v0, ?v2)))
tff(axiom525,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$h'(A__questionmark_v0,A__questionmark_v3),'fun_app$h'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$h'(A__questionmark_v0,A__questionmark_v1),'fun_app$h'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_real_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$i(?v0, ?v3) ≤ fun_app$i(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1)))) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$i(?v0, ?v1) ≤ fun_app$i(?v0, ?v2)))
tff(axiom526,axiom,
    ! [A__questionmark_v0: 'Nat_real_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$i'(A__questionmark_v0,A__questionmark_v3),'fun_app$i'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$i'(A__questionmark_v0,A__questionmark_v1),'fun_app$i'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$h(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1))) ≤ fun_app$h(?v0, ?v3)) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$h(?v0, ?v2) ≤ fun_app$h(?v0, ?v1)))
tff(axiom527,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$h'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))),'fun_app$h'(A__questionmark_v0,A__questionmark_v3))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$h'(A__questionmark_v0,A__questionmark_v2),'fun_app$h'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_real_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$i(?v0, nat$((fun_app$h(of_nat$, ?v3) + 1))) ≤ fun_app$i(?v0, ?v3)) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$i(?v0, ?v2) ≤ fun_app$i(?v0, ?v1)))
tff(axiom528,axiom,
    ! [A__questionmark_v0: 'Nat_real_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$i'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))),'fun_app$i'(A__questionmark_v0,A__questionmark_v3))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$i'(A__questionmark_v0,A__questionmark_v2),'fun_app$i'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (powr$(powr$(?v0, ?v1), ?v2) = powr$(powr$(?v0, ?v2), ?v1))
tff(axiom529,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] : ( 'powr$'('powr$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) = 'powr$'('powr$'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$h(of_nat$, nat$(?v0)) ≤ fun_app$h(of_nat$, nat$(?v1))))
tff(axiom530,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$','nat$'(A__questionmark_v1))) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom531,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((fun_app$h(of_nat$, nat$(?v0)) ≤ fun_app$h(of_nat$, ?v1)) = (?v0 ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom532,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq(A__questionmark_v0,'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom533,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$i(of_nat$a, ?v0) ≤ fun_app$i(of_nat$a, ?v1)))
tff(axiom534,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$i'('of_nat$a',A__questionmark_v0),'fun_app$i'('of_nat$a',A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((fun_app$h(of_nat$, nat$(?v0)) = fun_app$h(of_nat$, ?v1)) = (if (0 ≤ ?v0) (?v0 = fun_app$h(of_nat$, ?v1)) else (fun_app$h(of_nat$, ?v1) = 0)))
tff(axiom535,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
    <=> ( ( $lesseq(0,A__questionmark_v0)
         => ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) ) )
        & ( ~ $lesseq(0,A__questionmark_v0)
         => ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 ) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Int ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, nat$(?v1))) = (if (0 ≤ ?v1) (?v1 = fun_app$h(of_nat$, ?v0)) else (fun_app$h(of_nat$, ?v0) = 0)))
tff(axiom536,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $int] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)) )
    <=> ( ( $lesseq(0,A__questionmark_v1)
         => ( A__questionmark_v1 = 'fun_app$h'('of_nat$',A__questionmark_v0) ) )
        & ( ~ $lesseq(0,A__questionmark_v1)
         => ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 0 ) ) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((0 ≤ ?v0) ⇒ ((fun_app$h(of_nat$, nat$(?v0)) < fun_app$h(of_nat$, nat$(?v1))) = (?v0 < ?v1)))
tff(axiom537,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(0,A__questionmark_v0)
     => ( $less('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)))
      <=> $less(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$b(fun_app$k(less_eq$, zero$k), ?v2) ∧ fun_app$b(fun_app$k(less_eq$, ?v2), one$e))) ⇒ fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v2), ?v1)), fun_app$l(power$(?v2), ?v0)))
tff(axiom538,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v2)
        & 'fun_app$b'('fun_app$k'('less_eq$',A__questionmark_v2),'one$e') )
     => 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Int (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ ((0 ≤ ?v2) ∧ (?v2 ≤ 1))) ⇒ (fun_app$h(power$a(?v2), ?v1) ≤ fun_app$h(power$a(?v2), ?v0)))
tff(axiom539,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $int] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq(0,A__questionmark_v2)
        & $lesseq(A__questionmark_v2,1) )
     => $lesseq('fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Real (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ ((0.0 ≤ ?v2) ∧ (?v2 ≤ 1.0))) ⇒ (fun_app$i(power$b(?v2), ?v1) ≤ fun_app$i(power$b(?v2), ?v0)))
tff(axiom540,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: $real] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq(0.0,A__questionmark_v2)
        & $lesseq(A__questionmark_v2,1.0) )
     => $lesseq('fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less$a, one$e), ?v0) ∧ fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v0), ?v1)), fun_app$l(power$(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom541,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less$a','one$e'),A__questionmark_v0)
        & 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2)) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ?v2:Nat$ (((1 < ?v0) ∧ (fun_app$h(power$a(?v0), ?v1) ≤ fun_app$h(power$a(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom542,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(1,A__questionmark_v0)
        & $lesseq('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1),'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2)) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ?v2:Nat$ (((1.0 < ?v0) ∧ (fun_app$i(power$b(?v0), ?v1) ≤ fun_app$i(power$b(?v0), ?v2))) ⇒ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom543,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $less(1.0,A__questionmark_v0)
        & $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2)) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ¬(0 ≤ -fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v0) + 1))))
tff(axiom544,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $lesseq(0,$uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1))))) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 ≤ ?v0) ⇒ ((fun_app$h(of_nat$, nat$(?v0)) < fun_app$h(of_nat$, ?v1)) = (?v0 < fun_app$h(of_nat$, ?v1))))
tff(axiom545,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0,A__questionmark_v0)
     => ( $less('fun_app$h'('of_nat$','nat$'(A__questionmark_v0)),'fun_app$h'('of_nat$',A__questionmark_v1))
      <=> $less(A__questionmark_v0,'fun_app$h'('of_nat$',A__questionmark_v1)) ) ) ).

%% (0 = fun_app$h(of_nat$, nat$(0)))
tff(axiom546,axiom,
    0 = 'fun_app$h'('of_nat$','nat$'(0)) ).

%% ¬(0.0 = -1.0)
tff(axiom547,axiom,
    0.0 != $uminus(1.0) ).

%% ¬(0 = -1)
tff(axiom548,axiom,
    0 != $uminus(1) ).

%% (1 = fun_app$h(of_nat$, nat$(1)))
tff(axiom549,axiom,
    1 = 'fun_app$h'('of_nat$','nat$'(1)) ).

%% ¬(1.0 < -1.0)
tff(axiom550,axiom,
    ~ $less(1.0,$uminus(1.0)) ).

%% ¬(1 < -1)
tff(axiom551,axiom,
    ~ $less(1,$uminus(1)) ).

%% (-1.0 < 1.0)
tff(axiom552,axiom,
    $less($uminus(1.0),1.0) ).

%% (-1 < 1)
tff(axiom553,axiom,
    $less($uminus(1),1) ).

%% (0 ≤ 1)
tff(axiom554,axiom,
    $lesseq(0,1) ).

%% (0.0 ≤ 1.0)
tff(axiom555,axiom,
    $lesseq(0.0,1.0) ).

%% (0 ≤ 1)
tff(axiom556,axiom,
    $lesseq(0,1) ).

%% (0.0 ≤ 1.0)
tff(axiom557,axiom,
    $lesseq(0.0,1.0) ).

%% ¬(1 ≤ 0)
tff(axiom558,axiom,
    ~ $lesseq(1,0) ).

%% ¬(1.0 ≤ 0.0)
tff(axiom559,axiom,
    ~ $lesseq(1.0,0.0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$b(fun_app$k(less_eq$, zero$k), ?v0) ⇒ fun_app$b(fun_app$k(less_eq$, zero$k), fun_app$l(power$(?v0), ?v1)))
tff(axiom560,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v0)
     => 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((0 ≤ ?v0) ⇒ (0 ≤ fun_app$h(power$a(?v0), ?v1)))
tff(axiom561,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0,A__questionmark_v0)
     => $lesseq(0,'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((0.0 ≤ ?v0) ⇒ (0.0 ≤ fun_app$i(power$b(?v0), ?v1)))
tff(axiom562,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0.0,A__questionmark_v0)
     => $lesseq(0.0,'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(fun_app$k(less_eq$, ?v0), ?v1) ∧ fun_app$b(fun_app$k(less_eq$, zero$k), ?v0)) ⇒ fun_app$b(fun_app$k(less_eq$, fun_app$l(power$(?v0), ?v2)), fun_app$l(power$(?v1), ?v2)))
tff(axiom563,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'('fun_app$k'('less_eq$',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$b'('fun_app$k'('less_eq$','zero$k'),A__questionmark_v0) )
     => 'fun_app$b'('fun_app$k'('less_eq$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v2)),'fun_app$l'('power$'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Nat$ (((?v0 ≤ ?v1) ∧ (0 ≤ ?v0)) ⇒ (fun_app$h(power$a(?v0), ?v2) ≤ fun_app$h(power$a(?v1), ?v2)))
tff(axiom564,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(0,A__questionmark_v0) )
     => $lesseq('fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v2),'fun_app$h'('power$a'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Nat$ (((?v0 ≤ ?v1) ∧ (0.0 ≤ ?v0)) ⇒ (fun_app$i(power$b(?v0), ?v2) ≤ fun_app$i(power$b(?v1), ?v2)))
tff(axiom565,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(0.0,A__questionmark_v0) )
     => $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v2),'fun_app$i'('power$b'(A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$h(of_nat$, ?v0))
tff(axiom566,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ (0.0 ≤ fun_app$i(of_nat$a, ?v0))
tff(axiom567,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0.0,'fun_app$i'('of_nat$a',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$b(fun_app$k(less_eq$, one$e), ?v0) ⇒ fun_app$b(fun_app$k(less_eq$, one$e), fun_app$l(power$(?v0), ?v1)))
tff(axiom568,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$b'('fun_app$k'('less_eq$','one$e'),A__questionmark_v0)
     => 'fun_app$b'('fun_app$k'('less_eq$','one$e'),'fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Nat$ ((1 ≤ ?v0) ⇒ (1 ≤ fun_app$h(power$a(?v0), ?v1)))
tff(axiom569,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(1,A__questionmark_v0)
     => $lesseq(1,'fun_app$h'('power$a'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((1.0 ≤ ?v0) ⇒ (1.0 ≤ fun_app$i(power$b(?v0), ?v1)))
tff(axiom570,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(1.0,A__questionmark_v0)
     => $lesseq(1.0,'fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int_bool_fun$ ?v1:Int ((∀ ?v2:Nat$ fun_app$a(?v0, fun_app$h(of_nat$, ?v2)) ∧ ∀ ?v2:Nat$ fun_app$a(?v0, -fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v2) + 1))))) ⇒ fun_app$a(?v0, ?v1))
tff(axiom571,axiom,
    ! [A__questionmark_v0: 'Int_bool_fun$',A__questionmark_v1: $int] :
      ( ( ! [A__questionmark_v2: 'Nat$'] : 'fun_app$a'(A__questionmark_v0,'fun_app$h'('of_nat$',A__questionmark_v2))
        & ! [A__questionmark_v2: 'Nat$'] : 'fun_app$a'(A__questionmark_v0,$uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))))) )
     => 'fun_app$a'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ ((?v0 = -fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v1) + 1)))) ⇒ false)) ⇒ false)
tff(axiom572,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((?v0 ≤ 0.0) ∧ ((0.0 < ?v1) ∧ (?v1 ≤ ?v2))) ⇒ (powr$(?v2, ?v0) ≤ powr$(?v1, ?v0)))
tff(axiom573,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $lesseq(A__questionmark_v0,0.0)
        & $less(0.0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq('powr$'(A__questionmark_v2,A__questionmark_v0),'powr$'(A__questionmark_v1,A__questionmark_v0)) ) ).

%% ∀ ?v0:Real ?v1:Real ?v2:Real (((0.0 < ?v0) ∧ ((0.0 ≤ ?v1) ∧ (?v1 < ?v2))) ⇒ (powr$(?v1, ?v0) < powr$(?v2, ?v0)))
tff(axiom574,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: $real,A__questionmark_v2: $real] :
      ( ( $less(0.0,A__questionmark_v0)
        & $lesseq(0.0,A__questionmark_v1)
        & $less(A__questionmark_v1,A__questionmark_v2) )
     => $less('powr$'(A__questionmark_v1,A__questionmark_v0),'powr$'(A__questionmark_v2,A__questionmark_v0)) ) ).

%% ∀ ?v0:Real (((0.0 ≤ ln$(?v0)) ∧ (0.0 < ?v0)) ⇒ (1.0 ≤ ?v0))
tff(axiom575,axiom,
    ! [A__questionmark_v0: $real] :
      ( ( $lesseq(0.0,'ln$'(A__questionmark_v0))
        & $less(0.0,A__questionmark_v0) )
     => $lesseq(1.0,A__questionmark_v0) ) ).

%% ∀ ?v0:Real ((0.0 < ?v0) ⇒ (ln$(?v0) ≤ ?v0))
tff(axiom576,axiom,
    ! [A__questionmark_v0: $real] :
      ( $less(0.0,A__questionmark_v0)
     => $lesseq('ln$'(A__questionmark_v0),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$b(?v0, ?v1) ∧ ¬fun_app$b(?v0, nat$(0))) ⇒ ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) ≤ fun_app$h(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v2)) ⇒ ¬fun_app$b(?v0, ?v3)) ∧ fun_app$b(?v0, ?v2))))
tff(axiom577,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
        & ~ 'fun_app$b'(A__questionmark_v0,'nat$'(0)) )
     => ? [A__questionmark_v2: 'Nat$'] :
          ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1))
          & ! [A__questionmark_v3: 'Nat$'] :
              ( $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2))
             => ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) )
          & 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) ⇒ ((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom578,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)) = (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom579,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$b(?v2, ?v0) ∧ ∀ ?v3:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ∧ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v1)) ∧ fun_app$b(?v2, ?v3))) ⇒ fun_app$b(?v2, nat$((fun_app$h(of_nat$, ?v3) + 1)))))) ⇒ fun_app$b(?v2, ?v1))
tff(axiom580,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'(A__questionmark_v2,A__questionmark_v0)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
              & $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v1))
              & 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) )
           => 'fun_app$b'(A__questionmark_v2,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))) ) )
     => 'fun_app$b'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$b(?v2, ?v1) ∧ ∀ ?v3:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ∧ ((fun_app$h(of_nat$, ?v3) < fun_app$h(of_nat$, ?v1)) ∧ fun_app$b(?v2, nat$((fun_app$h(of_nat$, ?v3) + 1))))) ⇒ fun_app$b(?v2, ?v3)))) ⇒ fun_app$b(?v2, ?v0))
tff(axiom581,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & 'fun_app$b'(A__questionmark_v2,A__questionmark_v1)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
              & $less('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v1))
              & 'fun_app$b'(A__questionmark_v2,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v3),1))) )
           => 'fun_app$b'(A__questionmark_v2,A__questionmark_v3) ) )
     => 'fun_app$b'(A__questionmark_v2,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)))
tff(axiom582,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ ((fun_app$h(of_nat$, ?v1) < (fun_app$h(of_nat$, ?v0) + 1)) = (fun_app$h(of_nat$, ?v1) = fun_app$h(of_nat$, ?v0))))
tff(axiom583,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => ( $less('fun_app$h'('of_nat$',A__questionmark_v1),$sum('fun_app$h'('of_nat$',A__questionmark_v0),1))
      <=> ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 'fun_app$h'('of_nat$',A__questionmark_v0) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)) = (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom584,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1))
    <=> $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, ?v1)) = ((fun_app$h(of_nat$, ?v0) + 1) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom585,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
    <=> $lesseq($sum('fun_app$h'('of_nat$',A__questionmark_v0),1),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) < (fun_app$h(of_nat$, ?v1) + 1)))
tff(axiom586,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
     => $less('fun_app$h'('of_nat$',A__questionmark_v0),$sum('fun_app$h'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ¬(fun_app$h(of_nat$, ?v0) < -fun_app$h(of_nat$, ?v1))
tff(axiom587,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : ~ $less('fun_app$h'('of_nat$',A__questionmark_v0),$uminus('fun_app$h'('of_nat$',A__questionmark_v1))) ).

%% ∀ ?v0:Int (((0 ≤ ?v0) ∧ ∀ ?v1:Nat$ ((?v0 = fun_app$h(of_nat$, ?v1)) ⇒ false)) ⇒ false)
tff(axiom588,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ((0 ≤ ?v0) ⇒ ∃ ?v1:Nat$ (?v0 = fun_app$h(of_nat$, ?v1)))
tff(axiom589,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(0,A__questionmark_v0)
     => ? [A__questionmark_v1: 'Nat$'] : ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((0 < ?v0) ⇒ ((fun_app$h(of_nat$, nat$(?v1)) < fun_app$h(of_nat$, nat$(?v0))) = (?v1 < ?v0)))
tff(axiom590,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $less(0,A__questionmark_v0)
     => ( $less('fun_app$h'('of_nat$','nat$'(A__questionmark_v1)),'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)))
      <=> $less(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Int ((fun_app$h(of_nat$, ?v0) < fun_app$h(of_nat$, nat$(?v1))) = (fun_app$h(of_nat$, ?v0) < ?v1))
tff(axiom591,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: $int] :
      ( $less('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$','nat$'(A__questionmark_v1)))
    <=> $less('fun_app$h'('of_nat$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ¬(0.0 < -1.0)
tff(axiom592,axiom,
    ~ $less(0.0,$uminus(1.0)) ).

%% ¬(0 < -1)
tff(axiom593,axiom,
    ~ $less(0,$uminus(1)) ).

%% (-1 < 0)
tff(axiom594,axiom,
    $less($uminus(1),0) ).

%% ∀ ?v0:Int ((∀ ?v1:Nat$ ((?v0 = fun_app$h(of_nat$, ?v1)) ⇒ false) ∧ ∀ ?v1:Nat$ (((0 < fun_app$h(of_nat$, ?v1)) ∧ (?v0 = -fun_app$h(of_nat$, ?v1))) ⇒ false)) ⇒ false)
tff(axiom595,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( $less(0,'fun_app$h'('of_nat$',A__questionmark_v1))
              & ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$',A__questionmark_v1)) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ((fun_app$b(?v0, ?v1) ∧ ¬fun_app$b(?v0, nat$(0))) ⇒ ∃ ?v2:Nat$ ((fun_app$h(of_nat$, ?v2) < fun_app$h(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v3) ≤ fun_app$h(of_nat$, ?v2)) ⇒ ¬fun_app$b(?v0, ?v3)) ∧ fun_app$b(?v0, nat$((fun_app$h(of_nat$, ?v2) + 1))))))
tff(axiom596,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
        & ~ 'fun_app$b'(A__questionmark_v0,'nat$'(0)) )
     => ? [A__questionmark_v2: 'Nat$'] :
          ( $less('fun_app$h'('of_nat$',A__questionmark_v2),'fun_app$h'('of_nat$',A__questionmark_v1))
          & ! [A__questionmark_v3: 'Nat$'] :
              ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2))
             => ~ 'fun_app$b'(A__questionmark_v0,A__questionmark_v3) )
          & 'fun_app$b'(A__questionmark_v0,'nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v2),1))) ) ) ).

%% ∀ ?v0:Real ?v1:Nat$ ((0.0 ≤ ?v0) ⇒ ((fun_app$i(power$b(?v0), ?v1) ≤ 1.0) = ((fun_app$h(of_nat$, ?v1) = 0) ∨ (?v0 ≤ 1.0))))
tff(axiom597,axiom,
    ! [A__questionmark_v0: $real,A__questionmark_v1: 'Nat$'] :
      ( $lesseq(0.0,A__questionmark_v0)
     => ( $lesseq('fun_app$i'('power$b'(A__questionmark_v0),A__questionmark_v1),1.0)
      <=> ( ( 'fun_app$h'('of_nat$',A__questionmark_v1) = 0 )
          | $lesseq(A__questionmark_v0,1.0) ) ) ) ).

%% ∀ ?v0:Int ((1 ≤ ?v0) = (0 < ?v0))
tff(axiom598,axiom,
    ! [A__questionmark_v0: $int] :
      ( $lesseq(1,A__questionmark_v0)
    <=> $less(0,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((0 + 1) ≤ fun_app$h(of_nat$, ?v0)) ⇒ ((0 + 1) ≤ fun_app$h(of_nat$, fun_app$l(power$(?v0), ?v1))))
tff(axiom599,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum(0,1),'fun_app$h'('of_nat$',A__questionmark_v0))
     => $lesseq($sum(0,1),'fun_app$h'('of_nat$','fun_app$l'('power$'(A__questionmark_v0),A__questionmark_v1))) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Int (fun_app$b(?v0, nat$(?v1)) = (∀ ?v2:Nat$ ((?v1 = fun_app$h(of_nat$, ?v2)) ⇒ fun_app$b(?v0, ?v2)) ∧ ((?v1 < 0) ⇒ fun_app$b(?v0, nat$(0)))))
tff(axiom600,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: $int] :
      ( 'fun_app$b'(A__questionmark_v0,'nat$'(A__questionmark_v1))
    <=> ( ! [A__questionmark_v2: 'Nat$'] :
            ( ( A__questionmark_v1 = 'fun_app$h'('of_nat$',A__questionmark_v2) )
           => 'fun_app$b'(A__questionmark_v0,A__questionmark_v2) )
        & ( $less(A__questionmark_v1,0)
         => 'fun_app$b'(A__questionmark_v0,'nat$'(0)) ) ) ) ).

%% ∀ ?v0:Int ((((?v0 = 0) ⇒ false) ∧ (∀ ?v1:Nat$ (((?v0 = fun_app$h(of_nat$, ?v1)) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ false) ∧ ∀ ?v1:Nat$ (((?v0 = -fun_app$h(of_nat$, ?v1)) ∧ (0 < fun_app$h(of_nat$, ?v1))) ⇒ false))) ⇒ false)
tff(axiom601,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( ( ( A__questionmark_v0 = 0 )
         => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$h'('of_nat$',A__questionmark_v1) )
              & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false )
        & ! [A__questionmark_v1: 'Nat$'] :
            ( ( ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$',A__questionmark_v1)) )
              & $less(0,'fun_app$h'('of_nat$',A__questionmark_v1)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ((?v0 < 0) ⇒ ∃ ?v1:Nat$ (?v0 = -fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v1) + 1)))))
tff(axiom602,axiom,
    ! [A__questionmark_v0: $int] :
      ( $less(A__questionmark_v0,0)
     => ? [A__questionmark_v1: 'Nat$'] : ( A__questionmark_v0 = $uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v1),1)))) ) ) ).

%% ∀ ?v0:Nat$ (-fun_app$h(of_nat$, nat$((fun_app$h(of_nat$, ?v0) + 1))) < 0)
tff(axiom603,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $less($uminus('fun_app$h'('of_nat$','nat$'($sum('fun_app$h'('of_nat$',A__questionmark_v0),1)))),0) ).

%% ∀ ?v0:Nat$ ((1.0 ≤ fun_app$i(of_nat$a, ?v0)) = (1 ≤ fun_app$h(of_nat$, ?v0)))
tff(axiom604,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( $lesseq(1.0,'fun_app$i'('of_nat$a',A__questionmark_v0))
    <=> $lesseq(1,'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ?v2:Nat$ ((fun_app$b(?v0, ?v1) ∧ ∀ ?v3:Nat$ (fun_app$b(?v0, ?v3) ⇒ (fun_app$h(of_nat$, ?v3) ≤ fun_app$h(of_nat$, ?v2)))) ⇒ ∃ ?v3:Nat$ (fun_app$b(?v0, ?v3) ∧ ∀ ?v4:Nat$ (fun_app$b(?v0, ?v4) ⇒ (fun_app$h(of_nat$, ?v4) ≤ fun_app$h(of_nat$, ?v3)))))
tff(axiom605,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v3)
           => $lesseq('fun_app$h'('of_nat$',A__questionmark_v3),'fun_app$h'('of_nat$',A__questionmark_v2)) ) )
     => ? [A__questionmark_v3: 'Nat$'] :
          ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v3)
          & ! [A__questionmark_v4: 'Nat$'] :
              ( 'fun_app$b'(A__questionmark_v0,A__questionmark_v4)
             => $lesseq('fun_app$h'('of_nat$',A__questionmark_v4),'fun_app$h'('of_nat$',A__questionmark_v3)) ) ) ) ).

%% ∀ ?v0:Real_set$ ((∃ ?v1:Real member$(?v1, ?v0) ∧ ∃ ?v1:Real ∀ ?v2:Real (member$(?v2, ?v0) ⇒ (?v2 ≤ ?v1))) ⇒ ∃ ?v1:Real (∀ ?v2:Real (member$(?v2, ?v0) ⇒ (?v2 ≤ ?v1)) ∧ ∀ ?v2:Real (∀ ?v3:Real (member$(?v3, ?v0) ⇒ (?v3 ≤ ?v2)) ⇒ (?v1 ≤ ?v2))))
tff(axiom606,axiom,
    ! [A__questionmark_v0: 'Real_set$'] :
      ( ( ? [A__questionmark_v1: $real] : 'member$'(A__questionmark_v1,A__questionmark_v0)
        & ? [A__questionmark_v1: $real] :
          ! [A__questionmark_v2: $real] :
            ( 'member$'(A__questionmark_v2,A__questionmark_v0)
           => $lesseq(A__questionmark_v2,A__questionmark_v1) ) )
     => ? [A__questionmark_v1: $real] :
          ( ! [A__questionmark_v2: $real] :
              ( 'member$'(A__questionmark_v2,A__questionmark_v0)
             => $lesseq(A__questionmark_v2,A__questionmark_v1) )
          & ! [A__questionmark_v2: $real] :
              ( ! [A__questionmark_v3: $real] :
                  ( 'member$'(A__questionmark_v3,A__questionmark_v0)
                 => $lesseq(A__questionmark_v3,A__questionmark_v2) )
             => $lesseq(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∨ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v0)))
tff(axiom607,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
      | $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v0))) ⇒ (fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)))
tff(axiom608,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v0)) )
     => ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$h(of_nat$, ?v0) = fun_app$h(of_nat$, ?v1)) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)))
tff(axiom609,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$h'('of_nat$',A__questionmark_v0) = 'fun_app$h'('of_nat$',A__questionmark_v1) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v1)) ∧ (fun_app$h(of_nat$, ?v1) ≤ fun_app$h(of_nat$, ?v2))) ⇒ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v2)))
tff(axiom610,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v1))
        & $lesseq('fun_app$h'('of_nat$',A__questionmark_v1),'fun_app$h'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ (fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v0))
tff(axiom611,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat_real_fun$ ?v2:Nat_real_fun$ ((∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ⇒ (fun_app$i(?v1, ?v3) < fun_app$i(?v2, ?v3))) ∧ ∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ⇒ (fun_app$i(?v2, ?v3) ≤ fun_app$i(?v2, ?v0)))) ⇒ ∀ ?v3:Nat$ ((fun_app$h(of_nat$, ?v0) ≤ fun_app$h(of_nat$, ?v3)) ⇒ (fun_app$i(?v1, ?v3) < fun_app$i(?v2, ?v0))))
tff(axiom612,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_real_fun$',A__questionmark_v2: 'Nat_real_fun$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] :
            ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
           => $less('fun_app$i'(A__questionmark_v1,A__questionmark_v3),'fun_app$i'(A__questionmark_v2,A__questionmark_v3)) )
        & ! [A__questionmark_v3: 'Nat$'] :
            ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
           => $lesseq('fun_app$i'(A__questionmark_v2,A__questionmark_v3),'fun_app$i'(A__questionmark_v2,A__questionmark_v0)) ) )
     => ! [A__questionmark_v3: 'Nat$'] :
          ( $lesseq('fun_app$h'('of_nat$',A__questionmark_v0),'fun_app$h'('of_nat$',A__questionmark_v3))
         => $less('fun_app$i'(A__questionmark_v1,A__questionmark_v3),'fun_app$i'(A__questionmark_v2,A__questionmark_v0)) ) ) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$h(of_nat$, ?v0))
tff(axiom613,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$h'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ (nat$(fun_app$h(of_nat$, ?v0)) = ?v0)
tff(axiom614,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'nat$'('fun_app$h'('of_nat$',A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$h(of_nat$, nat$(?v0)) = (if (0 ≤ ?v0) ?v0 else 0))
tff(axiom615,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = A__questionmark_v0 ) )
      & ( ~ $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$h'('of_nat$','nat$'(A__questionmark_v0)) = 0 ) ) ) ).

%% ∀ b:tlbool ((b = tltrue) ∨ (b = tlfalse))
tff(formula_617,axiom,
    ! [B: tlbool] :
      ( ( B = tltrue )
      | ( B = tlfalse ) ) ).

%% ¬(tltrue = tlfalse)
tff(formula_618,axiom,
    tltrue != tlfalse ).

%------------------------------------------------------------------------------

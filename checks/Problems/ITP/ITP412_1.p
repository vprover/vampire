%------------------------------------------------------------------------------
% File     : ITP001_1 : TPTP v9.0.0. Released v8.1.0.
% Domain   : Interactive Theorem Proving
% Problem  : SMT-LIB TESL_Language Hygge_Theory 00122_005689
% Version  : [Des21] axioms.
% English  :

% Refs     : [Des21] Desharnais (2021), Email to Geoff Sutcliffe
% Source   : [Des21]
% Names    : TESL_Language-0010_Hygge_Theory-prob_00122_005689 [Des21]

% Status   : Theorem
% Rating   : 0.25 v8.2.0, 0.62 v8.1.0
% Syntax   : Number of formulae    :  894 ( 185 unt; 242 typ;   0 def)
%            Number of atoms       : 1706 ( 443 equ)
%            Maximal formula atoms :   19 (   2 avg)
%            Number of connectives : 1093 (  39   ~;   9   |; 386   &)
%                                         ( 156 <=>; 503  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   15 (   6 avg)
%            Maximal term depth    :    9 (   2 avg)
%            Number arithmetic     :  623 ( 260 atm;  40 fun;  44 num; 279 var)
%            Number of types       :   72 (  70 usr;   1 ari)
%            Number of type conns  :  237 ( 129   >; 108   *;   0   +;   0  <<)
%            Number of predicates  :   28 (  24 usr;   2 prp; 0-2 aty)
%            Number of functors    :  151 ( 148 usr;  45 con; 0-3 aty)
%            Number of variables   : 2061 (2028   !;  33   ?;2061   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Translated from SMT format using smttotptp 0.9.10. See
%            https://bitbucket.org/peba123/smttotptp/src/master/
%          : SMT-LIB AUFLIA logic
%------------------------------------------------------------------------------
%% Types:
tff('A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$': $tType ).

tff('Int_bool_fun$',type,
    'Int_bool_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun_fun$': $tType ).

tff('Nat_a_run_set_fun$',type,
    'Nat_a_run_set_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$': $tType ).

tff('Nat_nat_bool_fun_fun$',type,
    'Nat_nat_bool_fun_fun$': $tType ).

tff('A_TESL_atomic_a_TESL_atomic_fun_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',type,
    'A_TESL_atomic_a_TESL_atomic_fun_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$': $tType ).

tff('A_run_set_int_fun$',type,
    'A_run_set_int_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_fun$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$': $tType ).

tff('Clock$',type,
    'Clock$': $tType ).

tff('A_TESL_atomic_list_list$',type,
    'A_TESL_atomic_list_list$': $tType ).

tff('A_constr_a_constr_bool_fun_fun_a_constr_list_prod$',type,
    'A_constr_a_constr_bool_fun_fun_a_constr_list_prod$': $tType ).

tff('Nat_nat_nat_fun_fun$',type,
    'Nat_nat_nat_fun_fun$': $tType ).

tff('Nat_nat_prod_bool_fun$',type,
    'Nat_nat_prod_bool_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun_fun$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun_fun$': $tType ).

tff('A_constr_list$',type,
    'A_constr_list$': $tType ).

tff('A_TESL_atomic_list_a_constr_list_bool_fun_fun$',type,
    'A_TESL_atomic_list_a_constr_list_bool_fun_fun$': $tType ).

tff('A_TESL_atomic_a_TESL_atomic_bool_fun_fun$',type,
    'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$': $tType ).

tff('A_TESL_atomic_list$',type,
    'A_TESL_atomic_list$': $tType ).

tff('Int_int_fun$',type,
    'Int_int_fun$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_prod$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_prod$': $tType ).

tff('Nat_nat_prod$',type,
    'Nat_nat_prod$': $tType ).

tff('Nat_nat_prod_set$',type,
    'Nat_nat_prod_set$': $tType ).

tff('Cnt_expr$',type,
    'Cnt_expr$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$': $tType ).

tff('A_run$',type,
    'A_run$': $tType ).

tff('A_tag_const$',type,
    'A_tag_const$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$': $tType ).

tff('Nat_nat_fun$',type,
    'Nat_nat_fun$': $tType ).

tff('A_TESL_atomic_list_nat_prod$',type,
    'A_TESL_atomic_list_nat_prod$': $tType ).

tff('Int_nat_fun$',type,
    'Int_nat_fun$': $tType ).

tff('A_run_set_a_run_set_a_run_set_fun_fun$',type,
    'A_run_set_a_run_set_a_run_set_fun_fun$': $tType ).

tff('Nat$',type,
    'Nat$': $tType ).

tff('A_constr_list_a_TESL_atomic_list_bool_fun_fun$',type,
    'A_constr_list_a_TESL_atomic_list_bool_fun_fun$': $tType ).

tff('A_constr_list_a_constr_list_prod$',type,
    'A_constr_list_a_constr_list_prod$': $tType ).

tff('A_constr$',type,
    'A_constr$': $tType ).

tff('A_run_bool_fun_a_run_bool_fun_fun$',type,
    'A_run_bool_fun_a_run_bool_fun_fun$': $tType ).

tff('Int_a_run_set_fun$',type,
    'Int_a_run_set_fun$': $tType ).

tff(tlbool,type,
    tlbool: $tType ).

tff('A_TESL_atomic_a_TESL_atomic_fun$',type,
    'A_TESL_atomic_a_TESL_atomic_fun$': $tType ).

tff('A_run_set_a_run_set_fun$',type,
    'A_run_set_a_run_set_fun$': $tType ).

tff('A_constr_list_a_constr_list_bool_fun_fun$',type,
    'A_constr_list_a_constr_list_bool_fun_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$': $tType ).

tff('A_TESL_atomic_list_bool_fun$',type,
    'A_TESL_atomic_list_bool_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun_fun$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun_fun$': $tType ).

tff('A_constr_a_constr_bool_fun_fun$',type,
    'A_constr_a_constr_bool_fun_fun$': $tType ).

tff('A_run_set_nat_fun$',type,
    'A_run_set_nat_fun$': $tType ).

tff('A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun_fun$',type,
    'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun_fun$': $tType ).

tff('A_run_set$',type,
    'A_run_set$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$': $tType ).

tff('Bool_bool_fun$',type,
    'Bool_bool_fun$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$': $tType ).

tff('A_TESL_atomic$',type,
    'A_TESL_atomic$': $tType ).

tff('A_run_bool_fun$',type,
    'A_run_bool_fun$': $tType ).

tff('Int_int_int_fun_fun$',type,
    'Int_int_int_fun_fun$': $tType ).

tff('A_constr_list_bool_fun$',type,
    'A_constr_list_bool_fun$': $tType ).

tff('Int_int_bool_fun_fun$',type,
    'Int_int_bool_fun_fun$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$': $tType ).

tff('Nat_bool_fun$',type,
    'Nat_bool_fun$': $tType ).

tff('A_constr_list_list$',type,
    'A_constr_list_list$': $tType ).

tff('Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_fun$',type,
    'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_fun$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_a_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_a_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_fun$': $tType ).

tff('Nat_int_fun$',type,
    'Nat_int_fun$': $tType ).

tff('A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$',type,
    'A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$': $tType ).

tff('A_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun$',type,
    'A_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun$': $tType ).

%% Declarations:
tff('fun_app$g',type,
    'fun_app$g': ( 'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun$' * 'A_TESL_atomic_list$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ).

tff('inf$d',type,
    'inf$d': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_fun$' ).

tff('uuh$',type,
    'uuh$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ).

tff('fun_app$l',type,
    'fun_app$l': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun_fun$' * 'Nat$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun$' ).

tff('fun_app$i',type,
    'fun_app$i': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ) > $o ).

tff('case_prod$a',type,
    'case_prod$a': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('psi_1$',type,
    'psi_1$': 'A_TESL_atomic_list$' ).

tff('less_eq$c',type,
    'less_eq$c': ( 'A_run_bool_fun$' * 'A_run_bool_fun$' ) > $o ).

tff('bot$a',type,
    'bot$a': 'A_run_set$' ).

tff('fun_app$p',type,
    'fun_app$p': ( 'Bool_bool_fun$' * tlbool ) > $o ).

tff('uuk$',type,
    'uuk$': 'A_run_bool_fun$' ).

tff(def_3,type,
    def_3: ( 'A_run_bool_fun$' * 'A_run$' ) > tlbool ).

tff('collect$a',type,
    'collect$a': 'Nat_nat_prod_bool_fun$' > 'Nat_nat_prod_set$' ).

tff('fun_app$c',type,
    'fun_app$c': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' ).

tff('gamma_1$',type,
    'gamma_1$': 'A_constr_list$' ).

tff('sup$d',type,
    'sup$d': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ).

tff('inf$m',type,
    'inf$m': tlbool > 'Bool_bool_fun$' ).

tff('implies$',type,
    'implies$': ( 'Clock$' * 'Clock$' ) > 'A_TESL_atomic$' ).

tff('fun_app$x',type,
    'fun_app$x': ( 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_a_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ).

tff('strictlyPrecedes$',type,
    'strictlyPrecedes$': ( 'Clock$' * 'Clock$' ) > 'A_TESL_atomic$' ).

tff('fun_app$ad',type,
    'fun_app$ad': ( 'Int_int_int_fun_fun$' * $int ) > 'Int_int_fun$' ).

tff('cons$b',type,
    'cons$b': ( 'A_TESL_atomic_list$' * 'A_TESL_atomic_list_list$' ) > 'A_TESL_atomic_list_list$' ).

tff('bot$f',type,
    'bot$f': 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ).

tff(def_1,type,
    def_1: ( 'Nat_nat_bool_fun_fun$' * 'Nat$' * 'Nat$' ) > tlbool ).

tff('fun_app$ab',type,
    'fun_app$ab': ( 'Nat_nat_nat_fun_fun$' * 'Nat$' ) > 'Nat_nat_fun$' ).

tff('uui$',type,
    'uui$': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ).

tff('inf$e',type,
    'inf$e': ( 'Nat_nat_bool_fun_fun$' * 'Nat_nat_bool_fun_fun$' ) > 'Nat_nat_bool_fun_fun$' ).

tff('fun_app$m',type,
    'fun_app$m': ( 'Nat_bool_fun$' * 'Nat$' ) > $o ).

tff('operational_semantics_elim$',type,
    'operational_semantics_elim$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('member$',type,
    'member$': ( 'A_run$' * 'A_run_set$' ) > $o ).

tff('fun_app$o',type,
    'fun_app$o': ( 'Nat_nat_prod_bool_fun$' * 'Nat_nat_prod$' ) > $o ).

tff(def_5,type,
    def_5: ( 'Nat_nat_bool_fun_fun$' * 'Nat$' * 'Nat$' ) > tlbool ).

tff('collect$',type,
    'collect$': 'A_run_bool_fun$' > 'A_run_set$' ).

tff('less_eq$',type,
    'less_eq$': ( 'A_run_set$' * 'A_run_set$' ) > $o ).

tff('heronConf_interpretation$',type,
    'heronConf_interpretation$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' > 'A_run_set$' ).

tff('inf$g',type,
    'inf$g': 'Int_int_int_fun_fun$' ).

tff('less_eq$h',type,
    'less_eq$h': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ) > $o ).

tff('case_prod$b',type,
    'case_prod$b': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' ).

tff('fun_app$z',type,
    'fun_app$z': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ).

tff('fun_app$k',type,
    'fun_app$k': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ).

tff('n_1$',type,
    'n_1$': 'Nat$' ).

tff('ticks$',type,
    'ticks$': ( 'Clock$' * 'Nat$' ) > 'A_constr$' ).

tff('n$',type,
    'n$': 'Nat$' ).

tff('inf$k',type,
    'inf$k': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' ).

tff('cons$c',type,
    'cons$c': ( 'A_constr_list$' * 'A_constr_list_list$' ) > 'A_constr_list_list$' ).

tff('fun_app$u',type,
    'fun_app$u': ( 'Nat_int_fun$' * 'Nat$' ) > $int ).

tff('nil$a',type,
    'nil$a': 'A_constr_list$' ).

tff('less_eq$e',type,
    'less_eq$e': ( 'Nat_nat_bool_fun_fun$' * 'Nat_nat_bool_fun_fun$' ) > $o ).

tff('nat$',type,
    'nat$': 'Int_nat_fun$' ).

tff('fun_app$a',type,
    'fun_app$a': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ) > $o ).

tff('fun_app$ag',type,
    'fun_app$ag': ( 'Int_a_run_set_fun$' * $int ) > 'A_run_set$' ).

tff('tESL_interpretation_stepwise$',type,
    'tESL_interpretation_stepwise$': 'A_TESL_atomic_list$' > 'Nat_a_run_set_fun$' ).

tff('fun_app$ae',type,
    'fun_app$ae': ( 'Int_bool_fun$' * $int ) > $o ).

tff('case_prod$d',type,
    'case_prod$d': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun_fun$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' ).

tff('weaklyPrecedes$',type,
    'weaklyPrecedes$': ( 'Clock$' * 'Clock$' ) > 'A_TESL_atomic$' ).

tff('fun_app$j',type,
    'fun_app$j': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' * 'Nat$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' ).

tff('k_2$',type,
    'k_2$': 'Clock$' ).

tff('sporadicOn$',type,
    'sporadicOn$': ( 'Clock$' * 'A_tag_const$' * 'Clock$' ) > 'A_TESL_atomic$' ).

tff('impliesNot$',type,
    'impliesNot$': ( 'Clock$' * 'Clock$' ) > 'A_TESL_atomic$' ).

tff('operational_semantics_step$',type,
    'operational_semantics_step$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('inf$l',type,
    'inf$l': ( 'A_TESL_atomic_list_bool_fun$' * 'A_TESL_atomic_list_bool_fun$' ) > 'A_TESL_atomic_list_bool_fun$' ).

tff('bot$c',type,
    'bot$c': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ).

tff('collect$b',type,
    'collect$b': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ).

tff('less_eq$g',type,
    'less_eq$g': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ) > $o ).

tff('of_nat$',type,
    'of_nat$': 'Nat_int_fun$' ).

tff('pair$d',type,
    'pair$d': ( 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$' * 'A_TESL_atomic_list$' ) > 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$' ).

tff('inf$n',type,
    'inf$n': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' ).

tff('pair$',type,
    'pair$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun_fun$' ).

tff('pair$a',type,
    'pair$a': 'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun_fun$' ).

tff('tickCntArith$',type,
    'tickCntArith$': ( 'Cnt_expr$' * 'Cnt_expr$' * 'Nat_nat_prod_bool_fun$' ) > 'A_constr$' ).

tff('operational_semantics_intro$',type,
    'operational_semantics_intro$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('cons$',type,
    'cons$': ( 'A_TESL_atomic$' * 'A_TESL_atomic_list$' ) > 'A_TESL_atomic_list$' ).

tff('accp$',type,
    'accp$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun_fun$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('fun_app$ai',type,
    'fun_app$ai': ( 'A_run_set_int_fun$' * 'A_run_set$' ) > $int ).

tff('case_prod$c',type,
    'case_prod$c': 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$' ).

tff('bot$',type,
    'bot$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ).

tff('sup$c',type,
    'sup$c': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ).

tff('inf$',type,
    'inf$': 'A_run_set_a_run_set_a_run_set_fun_fun$' ).

tff('fun_app$ah',type,
    'fun_app$ah': ( 'A_run_set_nat_fun$' * 'A_run_set$' ) > 'Nat$' ).

tff('phi_1$',type,
    'phi_1$': 'A_TESL_atomic_list$' ).

tff('pair$e',type,
    'pair$e': ( 'A_constr_a_constr_bool_fun_fun$' * 'A_constr_list$' ) > 'A_constr_a_constr_bool_fun_fun_a_constr_list_prod$' ).

tff('inf$c',type,
    'inf$c': 'A_run_bool_fun$' > 'A_run_bool_fun_a_run_bool_fun_fun$' ).

tff('uue$',type,
    'uue$': ( 'A_run_set$' * 'A_run_bool_fun$' ) > 'A_run_bool_fun$' ).

tff('nil$',type,
    'nil$': 'A_TESL_atomic_list$' ).

tff('operational_semantics_elim_inv$',type,
    'operational_semantics_elim_inv$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' ).

tff('psi_2$',type,
    'psi_2$': 'A_TESL_atomic_list$' ).

tff(tltrue,type,
    tltrue: tlbool ).

tff('fun_app$v',type,
    'fun_app$v': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' ) > $o ).

tff('inf$a',type,
    'inf$a': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_fun$' ).

tff('fun_app$f',type,
    'fun_app$f': ( 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' * 'A_TESL_atomic_list$' ) > 'A_TESL_atomic_list_bool_fun$' ).

tff('uuc$',type,
    'uuc$': ( 'Bool_bool_fun$' * 'Nat_nat_bool_fun_fun$' ) > 'Nat_nat_bool_fun_fun$' ).

tff('phi_2$',type,
    'phi_2$': 'A_TESL_atomic_list$' ).

tff('n_2$',type,
    'n_2$': 'Nat$' ).

tff('member$a',type,
    'member$a': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ) > $o ).

tff('uud$',type,
    'uud$': 'A_run_set$' > 'A_run_bool_fun$' ).

tff('fun_app$am',type,
    'fun_app$am': ( 'A_constr_list_a_constr_list_bool_fun_fun$' * 'A_constr_list$' ) > 'A_constr_list_bool_fun$' ).

tff('fun_app$r',type,
    'fun_app$r': ( 'A_run_set_a_run_set_a_run_set_fun_fun$' * 'A_run_set$' ) > 'A_run_set_a_run_set_fun$' ).

tff('uub$',type,
    'uub$': 'Nat_nat_bool_fun_fun$' ).

tff('psi$',type,
    'psi$': 'A_TESL_atomic_list$' ).

tff('less_eq$d',type,
    'less_eq$d': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ) > $o ).

tff('inf$h',type,
    'inf$h': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ).

tff('uuf$',type,
    'uuf$': ( 'A_run_bool_fun$' * 'A_run_bool_fun$' ) > 'A_run_bool_fun$' ).

tff('gamma_2$',type,
    'gamma_2$': 'A_constr_list$' ).

tff('gamma$',type,
    'gamma$': 'A_constr_list$' ).

tff('sup$h',type,
    'sup$h': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ).

tff('bot$g',type,
    'bot$g': 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ).

tff('pair$h',type,
    'pair$h': ( 'A_TESL_atomic_a_TESL_atomic_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ) > 'A_TESL_atomic_a_TESL_atomic_fun_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ).

tff('fun_app$aa',type,
    'fun_app$aa': ( 'Nat_nat_fun$' * 'Nat$' ) > 'Nat$' ).

tff('less_eq$j',type,
    'less_eq$j': ( 'Nat_nat_prod_set$' * 'Nat_nat_prod_set$' ) > $o ).

tff('case_prod$f',type,
    'case_prod$f': ( 'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' ).

tff('sup$',type,
    'sup$': 'A_run_set_a_run_set_a_run_set_fun_fun$' ).

tff('less_eq$b',type,
    'less_eq$b': ( 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ) > $o ).

tff('fun_app$af',type,
    'fun_app$af': ( 'Int_int_bool_fun_fun$' * $int ) > 'Int_bool_fun$' ).

tff('pair$f',type,
    'pair$f': ( 'A_TESL_atomic_list$' * 'Nat$' ) > 'A_TESL_atomic_list_nat_prod$' ).

tff('fun_app$',type,
    'fun_app$': ( 'A_run_bool_fun$' * 'A_run$' ) > $o ).

tff('fun_app$w',type,
    'fun_app$w': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun_fun$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ).

tff('fun_app$ac',type,
    'fun_app$ac': ( 'Int_int_fun$' * $int ) > $int ).

tff('insert$a',type,
    'insert$a': 'A_run$' > 'A_run_set_a_run_set_fun$' ).

tff('bot$e',type,
    'bot$e': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ).

tff('nil$b',type,
    'nil$b': 'A_TESL_atomic_list_list$' ).

tff('sup$e',type,
    'sup$e': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ).

tff('member$c',type,
    'member$c': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ) > $o ).

tff('fun_app$n',type,
    'fun_app$n': ( 'Nat_nat_bool_fun_fun$' * 'Nat$' ) > 'Nat_bool_fun$' ).

tff('fun_app$aj',type,
    'fun_app$aj': ( 'A_constr_list_bool_fun$' * 'A_constr_list$' ) > $o ).

tff('sup$g',type,
    'sup$g': ( 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' * 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ).

tff(tlfalse,type,
    tlfalse: tlbool ).

tff('pair$c',type,
    'pair$c': ( 'Nat$' * 'Nat$' ) > 'Nat_nat_prod$' ).

tff('pair$g',type,
    'pair$g': ( 'A_constr_list$' * 'A_constr_list$' ) > 'A_constr_list_a_constr_list_prod$' ).

tff(def_2,type,
    def_2: ( 'A_run_bool_fun$' * 'A_run$' ) > tlbool ).

tff('insert$',type,
    'insert$': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ).

tff('case_prod$',type,
    'case_prod$': 'Nat_nat_bool_fun_fun$' > 'Nat_nat_prod_bool_fun$' ).

tff('nil$c',type,
    'nil$c': 'A_constr_list_list$' ).

tff('tickCountLeq$',type,
    'tickCountLeq$': ( 'Clock$' * 'Nat$' ) > 'Cnt_expr$' ).

tff('notTicks$',type,
    'notTicks$': ( 'Clock$' * 'Nat$' ) > 'A_constr$' ).

tff('bot$d',type,
    'bot$d': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$' ).

tff('inf$j',type,
    'inf$j': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ) > 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ).

tff('uu$',type,
    'uu$': ( tlbool * 'Nat_nat_bool_fun_fun$' ) > 'Nat_nat_bool_fun_fun$' ).

tff('fun_app$s',type,
    'fun_app$s': ( 'Nat_a_run_set_fun$' * 'Nat$' ) > 'A_run_set$' ).

tff('fun_app$d',type,
    'fun_app$d': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun_fun$' * 'A_constr_list$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_fun$' ).

tff('sup$f',type,
    'sup$f': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ).

tff('pair$b',type,
    'pair$b': 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun_fun$' ).

tff('fun_app$q',type,
    'fun_app$q': ( 'A_run_set_a_run_set_fun$' * 'A_run_set$' ) > 'A_run_set$' ).

tff('timestamp$',type,
    'timestamp$': ( 'Clock$' * 'Nat$' * 'A_tag_const$' ) > 'A_constr$' ).

tff('fun_app$b',type,
    'fun_app$b': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' * 'A_constr_list$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$' ).

tff('less_eq$i',type,
    'less_eq$i': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$' ) > $o ).

tff('k_1$',type,
    'k_1$': 'Clock$' ).

tff('uug$',type,
    'uug$': ( 'A_run_set$' * 'A_run_set$' ) > 'A_run_bool_fun$' ).

tff(def_6,type,
    def_6: ( 'Nat_nat_bool_fun_fun$' * 'Nat_nat_prod$' ) > tlbool ).

tff('sup$a',type,
    'sup$a': 'Nat_nat_nat_fun_fun$' ).

tff('inf$f',type,
    'inf$f': 'Nat_nat_nat_fun_fun$' ).

tff('case_prod$e',type,
    'case_prod$e': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_fun_fun$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$' ).

tff('member$b',type,
    'member$b': ( 'A_TESL_atomic_list_a_TESL_atomic_list_prod$' * 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' ) > $o ).

tff('bot$b',type,
    'bot$b': 'Nat$' ).

tff('phi$',type,
    'phi$': 'A_TESL_atomic_list$' ).

tff(def_4,type,
    def_4: ( 'Nat_nat_bool_fun_fun$' * 'Nat_nat_prod$' ) > tlbool ).

tff('inf$b',type,
    'inf$b': 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' > 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_a_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun_fun$' ).

tff('inf$i',type,
    'inf$i': ( 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' * 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ) > 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$' ).

tff('fun_app$ak',type,
    'fun_app$ak': ( 'A_TESL_atomic_list_a_constr_list_bool_fun_fun$' * 'A_TESL_atomic_list$' ) > 'A_constr_list_bool_fun$' ).

tff('fun_app$h',type,
    'fun_app$h': ( 'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun_fun$' * 'A_TESL_atomic_list$' ) > 'A_TESL_atomic_list_a_TESL_atomic_list_a_TESL_atomic_list_prod_fun$' ).

tff('tickCountLess$',type,
    'tickCountLess$': ( 'Clock$' * 'Nat$' ) > 'Cnt_expr$' ).

tff('fun_app$al',type,
    'fun_app$al': ( 'A_constr_list_a_TESL_atomic_list_bool_fun_fun$' * 'A_constr_list$' ) > 'A_TESL_atomic_list_bool_fun$' ).

tff('uuj$',type,
    'uuj$': 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$' > 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$' ).

tff('uua$',type,
    'uua$': 'Nat_nat_prod_bool_fun$' > 'Nat_nat_bool_fun_fun$' ).

tff('fun_app$t',type,
    'fun_app$t': ( 'Int_nat_fun$' * $int ) > 'Nat$' ).

tff('sup$b',type,
    'sup$b': 'Int_int_int_fun_fun$' ).

tff('less_eq$f',type,
    'less_eq$f': 'Nat_nat_bool_fun_fun$' ).

tff('heronConf_interpretation_rel$',type,
    'heronConf_interpretation_rel$': 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_a_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun_fun$' ).

tff('fun_app$y',type,
    'fun_app$y': ( 'A_run_bool_fun_a_run_bool_fun_fun$' * 'A_run_bool_fun$' ) > 'A_run_bool_fun$' ).

tff('cons$a',type,
    'cons$a': ( 'A_constr$' * 'A_constr_list$' ) > 'A_constr_list$' ).

tff('less_eq$a',type,
    'less_eq$a': ( 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' * 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$' ) > $o ).

tff('fun_app$e',type,
    'fun_app$e': ( 'A_TESL_atomic_list_bool_fun$' * 'A_TESL_atomic_list$' ) > $o ).

tff('symbolic_run_interpretation$',type,
    'symbolic_run_interpretation$': 'A_constr_list$' > 'A_run_set$' ).

%% Assertions:
%% ∀ ?v0:A_run_set$ ?v1:A_run$ (fun_app$(uud$(?v0), ?v1) = member$(?v1, ?v0))
tff(axiom0,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$'] :
      ( 'fun_app$'('uud$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'member$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ (fun_app$(uug$(?v0, ?v1), ?v2) = (member$(?v2, ?v0) ∧ member$(?v2, ?v1)))
tff(axiom1,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( 'fun_app$'('uug$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'member$'(A__questionmark_v2,A__questionmark_v0)
        & 'member$'(A__questionmark_v2,A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_bool_fun$ ?v2:A_run$ (fun_app$(uue$(?v0, ?v1), ?v2) = (member$(?v2, ?v0) ∧ fun_app$(?v1, ?v2)))
tff(axiom2,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run$'] :
      ( 'fun_app$'('uue$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'member$'(A__questionmark_v2,A__questionmark_v0)
        & 'fun_app$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$a(fun_app$b(uuh$(?v0), ?v1), ?v2) = member$a(fun_app$c(fun_app$d(pair$, ?v1), ?v2), ?v0))
tff(axiom3,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$a'('fun_app$b'('uuh$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),A__questionmark_v2),A__questionmark_v0) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ (fun_app$e(fun_app$f(uuj$(?v0), ?v1), ?v2) = member$b(fun_app$g(fun_app$h(pair$a, ?v1), ?v2), ?v0))
tff(axiom4,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( 'fun_app$e'('fun_app$f'('uuj$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),A__questionmark_v2),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$i(fun_app$j(uui$(?v0), ?v1), ?v2) = member$c(fun_app$k(fun_app$l(pair$b, ?v1), ?v2), ?v0))
tff(axiom5,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$i'('fun_app$j'('uui$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),A__questionmark_v2),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ ?v2:A_run$ (fun_app$(uuf$(?v0, ?v1), ?v2) = (fun_app$(?v0, ?v2) ∧ fun_app$(?v1, ?v2)))
tff(axiom6,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run$'] :
      ( 'fun_app$'('uuf$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
    <=> ( 'fun_app$'(A__questionmark_v0,A__questionmark_v2)
        & 'fun_app$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_prod_bool_fun$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(uua$(?v0), ?v1), ?v2) = fun_app$o(?v0, pair$c(?v1, ?v2)))
tff(axiom7,axiom,
    ! [A__questionmark_v0: 'Nat_nat_prod_bool_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('uua$'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> 'fun_app$o'(A__questionmark_v0,'pair$c'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Bool ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat$ ?v3:Nat$ (fun_app$m(fun_app$n(uu$(?v0, ?v1), ?v2), ?v3) = (?v0 ∧ fun_app$m(fun_app$n(?v1, ?v2), ?v3)))
tff(axiom8,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('uu$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2),A__questionmark_v3)
    <=> ( ( A__questionmark_v0 = tltrue )
        & 'fun_app$m'('fun_app$n'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) ) ) ).

%% ∀ ?v0:Bool_bool_fun$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat$ ?v3:Nat$ (fun_app$m(fun_app$n(uuc$(?v0, ?v1), ?v2), ?v3) = fun_app$p(?v0, fun_app$m(fun_app$n(?v1, ?v2), ?v3)))
tff(axiom9,axiom,
    ! [A__questionmark_v0: 'Bool_bool_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('uuc$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2),A__questionmark_v3)
    <=> 'fun_app$p'(A__questionmark_v0,def_1(A__questionmark_v1,A__questionmark_v2,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(uub$, ?v0), ?v1) = true)
tff(axiom10,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('uub$',A__questionmark_v0),A__questionmark_v1)
    <=> $true ) ).

%% ∀ ?v0:A_run$ (fun_app$(uuk$, ?v0) = true)
tff(axiom11,axiom,
    ! [A__questionmark_v0: 'A_run$'] :
      ( 'fun_app$'('uuk$',A__questionmark_v0)
    <=> $true ) ).

%% ¬less_eq$(fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, symbolic_run_interpretation$(gamma_2$)), fun_app$s(tESL_interpretation_stepwise$(psi_2$), n_2$))), fun_app$s(tESL_interpretation_stepwise$(phi_2$), fun_app$t(nat$, (fun_app$u(of_nat$, n_2$) + 1)))), fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, symbolic_run_interpretation$(gamma_1$)), fun_app$s(tESL_interpretation_stepwise$(psi_1$), n_1$))), fun_app$s(tESL_interpretation_stepwise$(phi_1$), fun_app$t(nat$, (fun_app$u(of_nat$, n_1$) + 1)))))
tff(conjecture12,conjecture,
    'less_eq$'('fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','symbolic_run_interpretation$'('gamma_2$')),'fun_app$s'('tESL_interpretation_stepwise$'('psi_2$'),'n_2$'))),'fun_app$s'('tESL_interpretation_stepwise$'('phi_2$'),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$','n_2$'),1)))),'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','symbolic_run_interpretation$'('gamma_1$')),'fun_app$s'('tESL_interpretation_stepwise$'('psi_1$'),'n_1$'))),'fun_app$s'('tESL_interpretation_stepwise$'('phi_1$'),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$','n_1$'),1))))) ).

%% fun_app$v(operational_semantics_step$(fun_app$c(fun_app$d(pair$, gamma_1$), fun_app$k(fun_app$l(pair$b, n_1$), fun_app$g(fun_app$h(pair$a, psi_1$), phi_1$)))), fun_app$c(fun_app$d(pair$, gamma_2$), fun_app$k(fun_app$l(pair$b, n_2$), fun_app$g(fun_app$h(pair$a, psi_2$), phi_2$))))
tff(axiom13,axiom,
    'fun_app$v'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$','gamma_1$'),'fun_app$k'('fun_app$l'('pair$b','n_1$'),'fun_app$g'('fun_app$h'('pair$a','psi_1$'),'phi_1$')))),'fun_app$c'('fun_app$d'('pair$','gamma_2$'),'fun_app$k'('fun_app$l'('pair$b','n_2$'),'fun_app$g'('fun_app$h'('pair$a','psi_2$'),'phi_2$')))) ).

%% fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, gamma_1$), fun_app$k(fun_app$l(pair$b, n_1$), fun_app$g(fun_app$h(pair$a, psi_1$), phi_1$)))), fun_app$c(fun_app$d(pair$, gamma_2$), fun_app$k(fun_app$l(pair$b, n_2$), fun_app$g(fun_app$h(pair$a, psi_2$), phi_2$))))
tff(axiom14,axiom,
    'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$','gamma_1$'),'fun_app$k'('fun_app$l'('pair$b','n_1$'),'fun_app$g'('fun_app$h'('pair$a','psi_1$'),'phi_1$')))),'fun_app$c'('fun_app$d'('pair$','gamma_2$'),'fun_app$k'('fun_app$l'('pair$b','n_2$'),'fun_app$g'('fun_app$h'('pair$a','psi_2$'),'phi_2$')))) ).

%% (fun_app$c(fun_app$d(pair$, gamma_1$), fun_app$k(fun_app$l(pair$b, n_1$), fun_app$g(fun_app$h(pair$a, psi_1$), phi_1$))) = fun_app$c(fun_app$d(pair$, gamma$), fun_app$k(fun_app$l(pair$b, n$), fun_app$g(fun_app$h(pair$a, cons$(weaklyPrecedes$(k_1$, k_2$), psi$)), phi$))))
tff(axiom15,axiom,
    'fun_app$c'('fun_app$d'('pair$','gamma_1$'),'fun_app$k'('fun_app$l'('pair$b','n_1$'),'fun_app$g'('fun_app$h'('pair$a','psi_1$'),'phi_1$'))) = 'fun_app$c'('fun_app$d'('pair$','gamma$'),'fun_app$k'('fun_app$l'('pair$b','n$'),'fun_app$g'('fun_app$h'('pair$a','cons$'('weaklyPrecedes$'('k_1$','k_2$'),'psi$')),'phi$'))) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)))
tff(axiom16,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v2:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (less_eq$a(?v0, fun_app$w(inf$a(?v1), ?v2)) = (less_eq$a(?v0, ?v1) ∧ less_eq$a(?v0, ?v2)))
tff(axiom17,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v2: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] :
      ( 'less_eq$a'(A__questionmark_v0,'fun_app$w'('inf$a'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$a'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$a'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (less_eq$b(?v0, fun_app$x(inf$b(?v1), ?v2)) = (less_eq$b(?v0, ?v1) ∧ less_eq$b(?v0, ?v2)))
tff(axiom18,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] :
      ( 'less_eq$b'(A__questionmark_v0,'fun_app$x'('inf$b'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$b'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$b'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ ?v2:A_run_bool_fun$ (less_eq$c(?v0, fun_app$y(inf$c(?v1), ?v2)) = (less_eq$c(?v0, ?v1) ∧ less_eq$c(?v0, ?v2)))
tff(axiom19,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run_bool_fun$'] :
      ( 'less_eq$c'(A__questionmark_v0,'fun_app$y'('inf$c'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$c'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$c'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (less_eq$d(?v0, fun_app$z(inf$d(?v1), ?v2)) = (less_eq$d(?v0, ?v1) ∧ less_eq$d(?v0, ?v2)))
tff(axiom20,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] :
      ( 'less_eq$d'(A__questionmark_v0,'fun_app$z'('inf$d'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$d'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$d'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_bool_fun_fun$ (less_eq$e(?v0, inf$e(?v1, ?v2)) = (less_eq$e(?v0, ?v1) ∧ less_eq$e(?v0, ?v2)))
tff(axiom21,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( 'less_eq$e'(A__questionmark_v0,'inf$e'(A__questionmark_v1,A__questionmark_v2))
    <=> ( 'less_eq$e'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$e'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)))
tff(axiom22,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)))
tff(axiom23,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)) = ((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)))
tff(axiom24,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2))
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v2:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (less_eq$a(?v0, fun_app$w(inf$a(?v1), ?v2)) = (less_eq$a(?v0, ?v1) ∧ less_eq$a(?v0, ?v2)))
tff(axiom25,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v2: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] :
      ( 'less_eq$a'(A__questionmark_v0,'fun_app$w'('inf$a'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$a'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$a'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (less_eq$b(?v0, fun_app$x(inf$b(?v1), ?v2)) = (less_eq$b(?v0, ?v1) ∧ less_eq$b(?v0, ?v2)))
tff(axiom26,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] :
      ( 'less_eq$b'(A__questionmark_v0,'fun_app$x'('inf$b'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$b'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$b'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ ?v2:A_run_bool_fun$ (less_eq$c(?v0, fun_app$y(inf$c(?v1), ?v2)) = (less_eq$c(?v0, ?v1) ∧ less_eq$c(?v0, ?v2)))
tff(axiom27,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run_bool_fun$'] :
      ( 'less_eq$c'(A__questionmark_v0,'fun_app$y'('inf$c'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$c'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$c'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (less_eq$d(?v0, fun_app$z(inf$d(?v1), ?v2)) = (less_eq$d(?v0, ?v1) ∧ less_eq$d(?v0, ?v2)))
tff(axiom28,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] :
      ( 'less_eq$d'(A__questionmark_v0,'fun_app$z'('inf$d'(A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$d'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$d'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_bool_fun_fun$ (less_eq$e(?v0, inf$e(?v1, ?v2)) = (less_eq$e(?v0, ?v1) ∧ less_eq$e(?v0, ?v2)))
tff(axiom29,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( 'less_eq$e'(A__questionmark_v0,'inf$e'(A__questionmark_v1,A__questionmark_v2))
    <=> ( 'less_eq$e'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$e'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)))
tff(axiom30,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)))
tff(axiom31,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)) = ((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)))
tff(axiom32,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2))
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% (((fun_app$v(operational_semantics_intro$(fun_app$c(fun_app$d(pair$, gamma_1$), fun_app$k(fun_app$l(pair$b, n_1$), fun_app$g(fun_app$h(pair$a, psi_1$), phi_1$)))), fun_app$c(fun_app$d(pair$, gamma_2$), fun_app$k(fun_app$l(pair$b, n_2$), fun_app$g(fun_app$h(pair$a, psi_2$), phi_2$)))) ⇒ false) ∧ (fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, gamma_1$), fun_app$k(fun_app$l(pair$b, n_1$), fun_app$g(fun_app$h(pair$a, psi_1$), phi_1$)))), fun_app$c(fun_app$d(pair$, gamma_2$), fun_app$k(fun_app$l(pair$b, n_2$), fun_app$g(fun_app$h(pair$a, psi_2$), phi_2$)))) ⇒ false)) ⇒ false)
tff(axiom33,axiom,
    ( ( ( 'fun_app$v'('operational_semantics_intro$'('fun_app$c'('fun_app$d'('pair$','gamma_1$'),'fun_app$k'('fun_app$l'('pair$b','n_1$'),'fun_app$g'('fun_app$h'('pair$a','psi_1$'),'phi_1$')))),'fun_app$c'('fun_app$d'('pair$','gamma_2$'),'fun_app$k'('fun_app$l'('pair$b','n_2$'),'fun_app$g'('fun_app$h'('pair$a','psi_2$'),'phi_2$'))))
       => $false )
      & ( 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$','gamma_1$'),'fun_app$k'('fun_app$l'('pair$b','n_1$'),'fun_app$g'('fun_app$h'('pair$a','psi_1$'),'phi_1$')))),'fun_app$c'('fun_app$d'('pair$','gamma_2$'),'fun_app$k'('fun_app$l'('pair$b','n_2$'),'fun_app$g'('fun_app$h'('pair$a','psi_2$'),'phi_2$'))))
       => $false ) )
   => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ((member$b(?v0, ?v1) ∧ member$b(?v0, ?v2)) ⇒ member$b(?v0, inf$h(?v1, ?v2)))
tff(axiom34,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( ( 'member$b'(A__questionmark_v0,A__questionmark_v1)
        & 'member$b'(A__questionmark_v0,A__questionmark_v2) )
     => 'member$b'(A__questionmark_v0,'inf$h'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ((member$c(?v0, ?v1) ∧ member$c(?v0, ?v2)) ⇒ member$c(?v0, inf$i(?v1, ?v2)))
tff(axiom35,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( ( 'member$c'(A__questionmark_v0,A__questionmark_v1)
        & 'member$c'(A__questionmark_v0,A__questionmark_v2) )
     => 'member$c'(A__questionmark_v0,'inf$i'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v2:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ((member$a(?v0, ?v1) ∧ member$a(?v0, ?v2)) ⇒ member$a(?v0, inf$j(?v1, ?v2)))
tff(axiom36,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v2: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( ( 'member$a'(A__questionmark_v0,A__questionmark_v1)
        & 'member$a'(A__questionmark_v0,A__questionmark_v2) )
     => 'member$a'(A__questionmark_v0,'inf$j'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ ((member$(?v0, ?v1) ∧ member$(?v0, ?v2)) ⇒ member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom37,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'member$'(A__questionmark_v0,A__questionmark_v1)
        & 'member$'(A__questionmark_v0,A__questionmark_v2) )
     => 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ (member$b(?v0, inf$h(?v1, ?v2)) = (member$b(?v0, ?v1) ∧ member$b(?v0, ?v2)))
tff(axiom38,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( 'member$b'(A__questionmark_v0,'inf$h'(A__questionmark_v1,A__questionmark_v2))
    <=> ( 'member$b'(A__questionmark_v0,A__questionmark_v1)
        & 'member$b'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ (member$c(?v0, inf$i(?v1, ?v2)) = (member$c(?v0, ?v1) ∧ member$c(?v0, ?v2)))
tff(axiom39,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( 'member$c'(A__questionmark_v0,'inf$i'(A__questionmark_v1,A__questionmark_v2))
    <=> ( 'member$c'(A__questionmark_v0,A__questionmark_v1)
        & 'member$c'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v2:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ (member$a(?v0, inf$j(?v1, ?v2)) = (member$a(?v0, ?v1) ∧ member$a(?v0, ?v2)))
tff(axiom40,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v2: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( 'member$a'(A__questionmark_v0,'inf$j'(A__questionmark_v1,A__questionmark_v2))
    <=> ( 'member$a'(A__questionmark_v0,A__questionmark_v1)
        & 'member$a'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = (member$(?v0, ?v1) ∧ member$(?v0, ?v2)))
tff(axiom41,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
    <=> ( 'member$'(A__questionmark_v0,A__questionmark_v1)
        & 'member$'(A__questionmark_v0,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v0) = ?v0)
tff(axiom42,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (fun_app$w(inf$a(?v0), ?v0) = ?v0)
tff(axiom43,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] : ( 'fun_app$w'('inf$a'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (fun_app$x(inf$b(?v0), ?v0) = ?v0)
tff(axiom44,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] : ( 'fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_bool_fun$ (fun_app$y(inf$c(?v0), ?v0) = ?v0)
tff(axiom45,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$'] : ( 'fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (fun_app$z(inf$d(?v0), ?v0) = ?v0)
tff(axiom46,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] : ( 'fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v0) = ?v0)
tff(axiom47,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v0) = ?v0)
tff(axiom48,axiom,
    ! [A__questionmark_v0: $int] : ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (fun_app$w(inf$a(?v0), ?v0) = ?v0)
tff(axiom49,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] : ( 'fun_app$w'('inf$a'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (fun_app$x(inf$b(?v0), ?v0) = ?v0)
tff(axiom50,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] : ( 'fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_bool_fun$ (fun_app$y(inf$c(?v0), ?v0) = ?v0)
tff(axiom51,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$'] : ( 'fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (fun_app$z(inf$d(?v0), ?v0) = ?v0)
tff(axiom52,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] : ( 'fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v0) = ?v0)
tff(axiom53,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1)) = fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1))
tff(axiom54,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1)) = 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (fun_app$w(inf$a(?v0), fun_app$w(inf$a(?v0), ?v1)) = fun_app$w(inf$a(?v0), ?v1))
tff(axiom55,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] : ( 'fun_app$w'('inf$a'(A__questionmark_v0),'fun_app$w'('inf$a'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$w'('inf$a'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (fun_app$x(inf$b(?v0), fun_app$x(inf$b(?v0), ?v1)) = fun_app$x(inf$b(?v0), ?v1))
tff(axiom56,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] : ( 'fun_app$x'('inf$b'(A__questionmark_v0),'fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ (fun_app$y(inf$c(?v0), fun_app$y(inf$c(?v0), ?v1)) = fun_app$y(inf$c(?v0), ?v1))
tff(axiom57,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$'] : ( 'fun_app$y'('inf$c'(A__questionmark_v0),'fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (fun_app$z(inf$d(?v0), fun_app$z(inf$d(?v0), ?v1)) = fun_app$z(inf$d(?v0), ?v1))
tff(axiom58,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] : ( 'fun_app$z'('inf$d'(A__questionmark_v0),'fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v1)) = 'fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom59,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)) ⇒ (?v0 = ?v1))
tff(axiom60,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ (∀ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (member$b(?v2, ?v0) ⇒ member$b(?v2, ?v1)) ⇒ less_eq$g(?v0, ?v1))
tff(axiom61,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( ! [A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
          ( 'member$b'(A__questionmark_v2,A__questionmark_v0)
         => 'member$b'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$g'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ (∀ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (member$c(?v2, ?v0) ⇒ member$c(?v2, ?v1)) ⇒ less_eq$h(?v0, ?v1))
tff(axiom62,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( ! [A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
          ( 'member$c'(A__questionmark_v2,A__questionmark_v0)
         => 'member$c'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$h'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ (∀ ?v2:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (member$a(?v2, ?v0) ⇒ member$a(?v2, ?v1)) ⇒ less_eq$i(?v0, ?v1))
tff(axiom63,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( ! [A__questionmark_v2: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
          ( 'member$a'(A__questionmark_v2,A__questionmark_v0)
         => 'member$a'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$i'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (∀ ?v2:A_run$ (member$(?v2, ?v0) ⇒ member$(?v2, ?v1)) ⇒ less_eq$(?v0, ?v1))
tff(axiom64,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ! [A__questionmark_v2: 'A_run$'] :
          ( 'member$'(A__questionmark_v2,A__questionmark_v0)
         => 'member$'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v2:A_constr_list$ (fun_app$b(fun_app$w(inf$a(?v0), ?v1), ?v2) = inf$k(fun_app$b(?v0, ?v2), fun_app$b(?v1, ?v2)))
tff(axiom65,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v2: 'A_constr_list$'] : ( 'fun_app$b'('fun_app$w'('inf$a'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2) = 'inf$k'('fun_app$b'(A__questionmark_v0,A__questionmark_v2),'fun_app$b'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v2:A_TESL_atomic_list$ (fun_app$f(fun_app$x(inf$b(?v0), ?v1), ?v2) = inf$l(fun_app$f(?v0, ?v2), fun_app$f(?v1, ?v2)))
tff(axiom66,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic_list$'] : ( 'fun_app$f'('fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2) = 'inf$l'('fun_app$f'(A__questionmark_v0,A__questionmark_v2),'fun_app$f'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ ?v2:A_run$ (fun_app$(fun_app$y(inf$c(?v0), ?v1), ?v2) = fun_app$p(inf$m(fun_app$(?v0, ?v2)), fun_app$(?v1, ?v2)))
tff(axiom67,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run$'] :
      ( 'fun_app$'('fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> 'fun_app$p'('inf$m'(def_2(A__questionmark_v0,A__questionmark_v2)),def_3(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v2:Nat$ (fun_app$j(fun_app$z(inf$d(?v0), ?v1), ?v2) = inf$n(fun_app$j(?v0, ?v2), fun_app$j(?v1, ?v2)))
tff(axiom68,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v2: 'Nat$'] : ( 'fun_app$j'('fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2) = 'inf$n'('fun_app$j'(A__questionmark_v0,A__questionmark_v2),'fun_app$j'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (fun_app$x(inf$b(fun_app$x(inf$b(?v0), ?v1)), ?v1) = fun_app$x(inf$b(?v0), ?v1))
tff(axiom69,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] : ( 'fun_app$x'('inf$b'('fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = 'fun_app$x'('inf$b'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ (fun_app$y(inf$c(fun_app$y(inf$c(?v0), ?v1)), ?v1) = fun_app$y(inf$c(?v0), ?v1))
tff(axiom70,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$'] : ( 'fun_app$y'('inf$c'('fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = 'fun_app$y'('inf$c'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (fun_app$z(inf$d(fun_app$z(inf$d(?v0), ?v1)), ?v1) = fun_app$z(inf$d(?v0), ?v1))
tff(axiom71,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] : ( 'fun_app$z'('inf$d'('fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = 'fun_app$z'('inf$d'(A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v1) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom72,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v1) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom73,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom74,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ (less_eq$(collect$(?v0), collect$(?v1)) = ∀ ?v2:A_run$ (fun_app$(?v0, ?v2) ⇒ fun_app$(?v1, ?v2)))
tff(axiom75,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$'] :
      ( 'less_eq$'('collect$'(A__questionmark_v0),'collect$'(A__questionmark_v1))
    <=> ! [A__questionmark_v2: 'A_run$'] :
          ( 'fun_app$'(A__questionmark_v0,A__questionmark_v2)
         => 'fun_app$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)))
tff(axiom76,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v2)) ⇒ less_eq$(?v0, ?v2))
tff(axiom77,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ (∀ ?v2:A_run$ (fun_app$(?v0, ?v2) ⇒ fun_app$(?v1, ?v2)) ⇒ less_eq$(collect$(?v0), collect$(?v1)))
tff(axiom78,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$'] :
      ( ! [A__questionmark_v2: 'A_run$'] :
          ( 'fun_app$'(A__questionmark_v0,A__questionmark_v2)
         => 'fun_app$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less_eq$'('collect$'(A__questionmark_v0),'collect$'(A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ less_eq$(?v0, ?v0)
tff(axiom79,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = ∀ ?v2:A_run$ (member$(?v2, ?v0) ⇒ member$(?v2, ?v1)))
tff(axiom80,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'A_run$'] :
          ( 'member$'(A__questionmark_v2,A__questionmark_v0)
         => 'member$'(A__questionmark_v2,A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) ⇒ less_eq$(?v1, ?v0))
tff(axiom81,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => 'less_eq$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) ⇒ less_eq$(?v0, ?v1))
tff(axiom82,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = ∀ ?v2:A_run$ (member$(?v2, ?v0) ⇒ member$(?v2, ?v1)))
tff(axiom83,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ! [A__questionmark_v2: 'A_run$'] :
          ( 'member$'(A__questionmark_v2,A__questionmark_v0)
         => 'member$'(A__questionmark_v2,A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (((?v0 = ?v1) ∧ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)) ⇒ false)) ⇒ false)
tff(axiom84,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
            & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ ((less_eq$(?v0, ?v1) ∧ member$(?v2, ?v0)) ⇒ member$(?v2, ?v1))
tff(axiom85,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'member$'(A__questionmark_v2,A__questionmark_v0) )
     => 'member$'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ ((less_eq$(?v0, ?v1) ∧ member$(?v2, ?v0)) ⇒ member$(?v2, ?v1))
tff(axiom86,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'member$'(A__questionmark_v2,A__questionmark_v0) )
     => 'member$'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom87,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom88,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = fun_app$q(fun_app$r(inf$, ?v1), ?v0))
tff(axiom89,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = fun_app$q(fun_app$r(inf$, ?v1), ?v0))
tff(axiom90,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom91,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom92,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = fun_app$q(fun_app$r(inf$, ?v1), ?v0))
tff(axiom93,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom94,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom95,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom96,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom97,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = fun_app$q(fun_app$r(inf$, ?v0), ?v1))
tff(axiom98,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = fun_app$q(fun_app$r(inf$, ?v1), ?v0))
tff(axiom99,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v0) = ?v0)
tff(axiom100,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom101,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ⇒ member$(?v0, ?v2))
tff(axiom102,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
     => 'member$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ⇒ member$(?v0, ?v1))
tff(axiom103,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
     => 'member$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ ((member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ∧ ((member$(?v0, ?v1) ∧ member$(?v0, ?v2)) ⇒ false)) ⇒ false)
tff(axiom104,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
        & ( ( 'member$'(A__questionmark_v0,A__questionmark_v1)
            & 'member$'(A__questionmark_v0,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v2), ?v0), ?v1))
tff(axiom105,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v2), ?v0)), ?v1))
tff(axiom106,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v2),A__questionmark_v0)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v2), ?v0) ≤ ?v1))
tff(axiom107,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v2),A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v2), ?v1))
tff(axiom108,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v2)), ?v1))
tff(axiom109,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v2) ≤ ?v1))
tff(axiom110,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(inf$, ?v1), ?v0) = ?v0))
tff(axiom111,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(inf$f, ?v1), ?v0) = ?v0))
tff(axiom112,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(inf$g, ?v1), ?v0) = ?v0))
tff(axiom113,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = ?v0))
tff(axiom114,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1) = ?v0))
tff(axiom115,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) = ?v0))
tff(axiom116,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v1)
tff(axiom117,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v1)
tff(axiom118,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v1)
tff(axiom119,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v0)
tff(axiom120,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v0)
tff(axiom121,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v0)
tff(axiom122,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (?v0 = fun_app$q(fun_app$r(inf$, ?v0), ?v1)))
tff(axiom123,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (?v0 = fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)))
tff(axiom124,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( A__questionmark_v0 = 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (?v0 = fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1)))
tff(axiom125,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( A__questionmark_v0 = 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom126,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)))
tff(axiom127,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)))
tff(axiom128,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v0,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom129,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)))
tff(axiom130,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)))
tff(axiom131,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v0,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ∧ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ false)) ⇒ false)
tff(axiom132,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
        & ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
            & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)) ∧ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ false)) ⇒ false)
tff(axiom133,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2))
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)) ∧ (((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)) ⇒ false)) ⇒ false)
tff(axiom134,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2))
        & ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
            & $lesseq(A__questionmark_v0,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), ?v0) = ?v0))
tff(axiom135,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(inf$f, ?v1), ?v0) = ?v0))
tff(axiom136,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v1), ?v0) = ?v0))
tff(axiom137,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = ?v0))
tff(axiom138,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1) = ?v0))
tff(axiom139,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) = ?v0))
tff(axiom140,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), ?v0) = ?v0))
tff(axiom141,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(inf$f, ?v1), ?v0) = ?v0))
tff(axiom142,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v1), ?v0) = ?v0))
tff(axiom143,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = ?v0))
tff(axiom144,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1) = ?v0))
tff(axiom145,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) = ?v0))
tff(axiom146,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = ?v0))
tff(axiom147,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1) = ?v0))
tff(axiom148,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) = ?v0))
tff(axiom149,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set_a_run_set_a_run_set_fun_fun$ ?v1:A_run_set$ ?v2:A_run_set$ ((∀ ?v3:A_run_set$ ?v4:A_run_set$ less_eq$(fun_app$q(fun_app$r(?v0, ?v3), ?v4), ?v3) ∧ (∀ ?v3:A_run_set$ ?v4:A_run_set$ less_eq$(fun_app$q(fun_app$r(?v0, ?v3), ?v4), ?v4) ∧ ∀ ?v3:A_run_set$ ?v4:A_run_set$ ?v5:A_run_set$ ((less_eq$(?v3, ?v4) ∧ less_eq$(?v3, ?v5)) ⇒ less_eq$(?v3, fun_app$q(fun_app$r(?v0, ?v4), ?v5))))) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), ?v2) = fun_app$q(fun_app$r(?v0, ?v1), ?v2)))
tff(axiom150,axiom,
    ! [A__questionmark_v0: 'A_run_set_a_run_set_a_run_set_fun_fun$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4),A__questionmark_v3)
        & ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4),A__questionmark_v4)
        & ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( ( 'less_eq$'(A__questionmark_v3,A__questionmark_v4)
              & 'less_eq$'(A__questionmark_v3,A__questionmark_v5) )
           => 'less_eq$'(A__questionmark_v3,'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)) ) )
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) = 'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_nat_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(?v0, ?v3), ?v4)), ?v3) ∧ (∀ ?v3:Nat$ ?v4:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(?v0, ?v3), ?v4)), ?v4) ∧ ∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v3), ?v4) ∧ fun_app$m(fun_app$n(less_eq$f, ?v3), ?v5)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v3), fun_app$aa(fun_app$ab(?v0, ?v4), ?v5))))) ⇒ (fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2) = fun_app$aa(fun_app$ab(?v0, ?v1), ?v2)))
tff(axiom151,axiom,
    ! [A__questionmark_v0: 'Nat_nat_nat_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v3)
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v4)
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v3),A__questionmark_v4)
              & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v3),A__questionmark_v5) )
           => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v3),'fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)) ) )
     => ( 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2) = 'fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int_int_int_fun_fun$ ?v1:Int ?v2:Int ((∀ ?v3:Int ?v4:Int (fun_app$ac(fun_app$ad(?v0, ?v3), ?v4) ≤ ?v3) ∧ (∀ ?v3:Int ?v4:Int (fun_app$ac(fun_app$ad(?v0, ?v3), ?v4) ≤ ?v4) ∧ ∀ ?v3:Int ?v4:Int ?v5:Int (((?v3 ≤ ?v4) ∧ (?v3 ≤ ?v5)) ⇒ (?v3 ≤ fun_app$ac(fun_app$ad(?v0, ?v4), ?v5))))) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2) = fun_app$ac(fun_app$ad(?v0, ?v1), ?v2)))
tff(axiom152,axiom,
    ! [A__questionmark_v0: 'Int_int_int_fun_fun$',A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ! [A__questionmark_v3: $int,A__questionmark_v4: $int] : $lesseq('fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4),A__questionmark_v3)
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int] : $lesseq('fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4),A__questionmark_v4)
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( ( $lesseq(A__questionmark_v3,A__questionmark_v4)
              & $lesseq(A__questionmark_v3,A__questionmark_v5) )
           => $lesseq(A__questionmark_v3,'fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)) ) )
     => ( 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2) = 'fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = fun_app$q(fun_app$r(inf$, ?v0), ?v1)) ⇒ less_eq$(?v0, ?v1))
tff(axiom153,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1))
tff(axiom154,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1)) ⇒ (?v0 ≤ ?v1))
tff(axiom155,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) )
     => $lesseq(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ ((?v0 = fun_app$q(fun_app$r(inf$, ?v0), ?v1)) ⇒ false)) ⇒ false)
tff(axiom156,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((?v0 = fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)) ⇒ false)) ⇒ false)
tff(axiom157,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( ( A__questionmark_v0 = 'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 ≤ ?v1) ∧ ((?v0 = fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1)) ⇒ false)) ⇒ false)
tff(axiom158,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( ( A__questionmark_v0 = 'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v2), ?v0), ?v1))
tff(axiom159,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v2), ?v0)), ?v1))
tff(axiom160,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v2),A__questionmark_v0)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v2), ?v0) ≤ ?v1))
tff(axiom161,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v2),A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v2), ?v1))
tff(axiom162,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v2)), ?v1))
tff(axiom163,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v2) ≤ ?v1))
tff(axiom164,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v2), fun_app$q(fun_app$r(inf$, ?v1), ?v3)))
tff(axiom165,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v2)), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v3)))
tff(axiom166,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v2)),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v3)) ⇒ (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v2) ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v3)))
tff(axiom167,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v3) )
     => $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v2),'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom168,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)))
tff(axiom169,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)))
tff(axiom170,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v0,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ∧ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ false)) ⇒ false)
tff(axiom171,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))
        & ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
            & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2)) ∧ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ false)) ⇒ false)
tff(axiom172,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2))
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)) ∧ (((?v0 ≤ ?v1) ∧ (?v0 ≤ ?v2)) ⇒ false)) ⇒ false)
tff(axiom173,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2))
        & ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
            & $lesseq(A__questionmark_v0,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v1)
tff(axiom174,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v1)
tff(axiom175,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v1)
tff(axiom176,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v0)
tff(axiom177,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v0)
tff(axiom178,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v0)
tff(axiom179,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v0)
tff(axiom180,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v0)
tff(axiom181,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v0)
tff(axiom182,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v1)
tff(axiom183,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), ?v1)
tff(axiom184,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) ).

%% ∀ ?v0:Int ?v1:Int (fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1) ≤ ?v1)
tff(axiom185,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq('fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_bool_fun$ ?v3:A_run_bool_fun$ ((less_eq$(?v0, ?v1) ∧ ∀ ?v4:A_run$ ((member$(?v4, ?v0) ∧ fun_app$(?v2, ?v4)) ⇒ fun_app$(?v3, ?v4))) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), collect$(?v2)), fun_app$q(fun_app$r(inf$, ?v1), collect$(?v3))))
tff(axiom186,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_bool_fun$',A__questionmark_v3: 'A_run_bool_fun$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v4: 'A_run$'] :
            ( ( 'member$'(A__questionmark_v4,A__questionmark_v0)
              & 'fun_app$'(A__questionmark_v2,A__questionmark_v4) )
           => 'fun_app$'(A__questionmark_v3,A__questionmark_v4) ) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'collect$'(A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'collect$'(A__questionmark_v3))) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v0, ?v2)) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom187,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = ?v0))
tff(axiom188,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), ?v0) = ?v0))
tff(axiom189,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v1)
tff(axiom190,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v1) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v1), ?v0)
tff(axiom191,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(inf$, ?v0), ?v2), fun_app$q(fun_app$r(inf$, ?v1), ?v3)))
tff(axiom192,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (fun_app$v(operational_semantics_step$(?v0), ?v1) = (∃ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ ?v6:A_constr_list$ ?v7:Nat$ ?v8:A_TESL_atomic_list$ ?v9:A_TESL_atomic_list$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))) ∧ ((?v1 = fun_app$c(fun_app$d(pair$, ?v6), fun_app$k(fun_app$l(pair$b, ?v7), fun_app$g(fun_app$h(pair$a, ?v8), ?v9)))) ∧ fun_app$v(operational_semantics_intro$(fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))), fun_app$c(fun_app$d(pair$, ?v6), fun_app$k(fun_app$l(pair$b, ?v7), fun_app$g(fun_app$h(pair$a, ?v8), ?v9)))))) ∨ ∃ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ ?v6:A_constr_list$ ?v7:Nat$ ?v8:A_TESL_atomic_list$ ?v9:A_TESL_atomic_list$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))) ∧ ((?v1 = fun_app$c(fun_app$d(pair$, ?v6), fun_app$k(fun_app$l(pair$b, ?v7), fun_app$g(fun_app$h(pair$a, ?v8), ?v9)))) ∧ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))), fun_app$c(fun_app$d(pair$, ?v6), fun_app$k(fun_app$l(pair$b, ?v7), fun_app$g(fun_app$h(pair$a, ?v8), ?v9))))))))
tff(axiom193,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( 'fun_app$v'('operational_semantics_step$'(A__questionmark_v0),A__questionmark_v1)
    <=> ( ? [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$',A__questionmark_v6: 'A_constr_list$',A__questionmark_v7: 'Nat$',A__questionmark_v8: 'A_TESL_atomic_list$',A__questionmark_v9: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5))) )
            & ( A__questionmark_v1 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v6),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v7),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v8),A__questionmark_v9))) )
            & 'fun_app$v'('operational_semantics_intro$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v6),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v7),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v8),A__questionmark_v9)))) )
        | ? [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$',A__questionmark_v6: 'A_constr_list$',A__questionmark_v7: 'Nat$',A__questionmark_v8: 'A_TESL_atomic_list$',A__questionmark_v9: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5))) )
            & ( A__questionmark_v1 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v6),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v7),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v8),A__questionmark_v9))) )
            & 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v6),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v7),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v8),A__questionmark_v9)))) ) ) ) ).

%% (fun_app$c(fun_app$d(pair$, gamma_2$), fun_app$k(fun_app$l(pair$b, n_2$), fun_app$g(fun_app$h(pair$a, psi_2$), phi_2$))) = fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(k_2$, n$), tickCountLeq$(k_1$, n$), case_prod$(less_eq$f)), gamma$)), fun_app$k(fun_app$l(pair$b, n$), fun_app$g(fun_app$h(pair$a, psi$), cons$(weaklyPrecedes$(k_1$, k_2$), phi$)))))
tff(axiom194,axiom,
    'fun_app$c'('fun_app$d'('pair$','gamma_2$'),'fun_app$k'('fun_app$l'('pair$b','n_2$'),'fun_app$g'('fun_app$h'('pair$a','psi_2$'),'phi_2$'))) = 'fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'('k_2$','n$'),'tickCountLeq$'('k_1$','n$'),'case_prod$'('less_eq$f')),'gamma$')),'fun_app$k'('fun_app$l'('pair$b','n$'),'fun_app$g'('fun_app$h'('pair$a','psi$'),'cons$'('weaklyPrecedes$'('k_1$','k_2$'),'phi$')))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ?v4:A_constr_list$ ?v5:Nat$ ?v6:A_TESL_atomic_list$ ?v7:A_TESL_atomic_list$ (fun_app$v(operational_semantics_intro$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3)))), fun_app$c(fun_app$d(pair$, ?v4), fun_app$k(fun_app$l(pair$b, ?v5), fun_app$g(fun_app$h(pair$a, ?v6), ?v7)))) ⇒ fun_app$v(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3)))), fun_app$c(fun_app$d(pair$, ?v4), fun_app$k(fun_app$l(pair$b, ?v5), fun_app$g(fun_app$h(pair$a, ?v6), ?v7)))))
tff(axiom195,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_constr_list$',A__questionmark_v5: 'Nat$',A__questionmark_v6: 'A_TESL_atomic_list$',A__questionmark_v7: 'A_TESL_atomic_list$'] :
      ( 'fun_app$v'('operational_semantics_intro$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v4),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v5),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v6),A__questionmark_v7))))
     => 'fun_app$v'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v4),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v5),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v6),A__questionmark_v7)))) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ?v4:A_constr_list$ ?v5:Nat$ ?v6:A_TESL_atomic_list$ ?v7:A_TESL_atomic_list$ (fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3)))), fun_app$c(fun_app$d(pair$, ?v4), fun_app$k(fun_app$l(pair$b, ?v5), fun_app$g(fun_app$h(pair$a, ?v6), ?v7)))) ⇒ fun_app$v(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3)))), fun_app$c(fun_app$d(pair$, ?v4), fun_app$k(fun_app$l(pair$b, ?v5), fun_app$g(fun_app$h(pair$a, ?v6), ?v7)))))
tff(axiom196,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_constr_list$',A__questionmark_v5: 'Nat$',A__questionmark_v6: 'A_TESL_atomic_list$',A__questionmark_v7: 'A_TESL_atomic_list$'] :
      ( 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v4),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v5),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v6),A__questionmark_v7))))
     => 'fun_app$v'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v4),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v5),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v6),A__questionmark_v7)))) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v1:A_constr_list$ ?v2:Nat$ ?v3:A_TESL_atomic_list$ ?v4:A_TESL_atomic_list$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v1), fun_app$k(fun_app$l(pair$b, ?v2), fun_app$g(fun_app$h(pair$a, ?v3), ?v4)))) ⇒ false) ⇒ false)
tff(axiom197,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),A__questionmark_v4))) )
         => $false )
     => $false ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v1:A_constr_list$ ?v2:Nat$ ?v3:A_TESL_atomic_list$ ?v4:A_TESL_atomic_list$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v1), fun_app$k(fun_app$l(pair$b, ?v2), fun_app$g(fun_app$h(pair$a, ?v3), ?v4)))) ⇒ false) ⇒ false)
tff(axiom198,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),A__questionmark_v4))) )
         => $false )
     => $false ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((fun_app$c(fun_app$d(pair$, ?v0), ?v1) = fun_app$c(fun_app$d(pair$, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom199,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ( 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((fun_app$k(fun_app$l(pair$b, ?v0), ?v1) = fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom200,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v0),A__questionmark_v1) = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ((fun_app$g(fun_app$h(pair$a, ?v0), ?v1) = fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom201,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( ( 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v0),A__questionmark_v1) = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((fun_app$c(fun_app$d(pair$, ?v0), ?v1) = fun_app$c(fun_app$d(pair$, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom202,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ( 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((fun_app$k(fun_app$l(pair$b, ?v0), ?v1) = fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom203,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v0),A__questionmark_v1) = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ((fun_app$g(fun_app$h(pair$a, ?v0), ?v1) = fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom204,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( ( 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v0),A__questionmark_v1) = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:Bool ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_prod$ (fun_app$o(case_prod$(uu$(?v0, ?v1)), ?v2) = (?v0 ∧ fun_app$o(case_prod$(?v1), ?v2)))
tff(axiom205,axiom,
    ! [A__questionmark_v0: tlbool,A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_prod$'] :
      ( 'fun_app$o'('case_prod$'('uu$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2)
    <=> ( ( A__questionmark_v0 = tltrue )
        & 'fun_app$o'('case_prod$'(A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ (fun_app$o(case_prod$(?v0), pair$c(?v1, ?v2)) = fun_app$m(fun_app$n(?v0, ?v1), ?v2))
tff(axiom206,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$o'('case_prod$'(A__questionmark_v0),'pair$c'(A__questionmark_v1,A__questionmark_v2))
    <=> 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$a(fun_app$b(?v0, ?v1), ?v2) ⇒ fun_app$v(case_prod$a(?v0), fun_app$c(fun_app$d(pair$, ?v1), ?v2)))
tff(axiom207,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$a'('fun_app$b'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
     => 'fun_app$v'('case_prod$a'(A__questionmark_v0),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$i(fun_app$j(?v0, ?v1), ?v2) ⇒ fun_app$a(case_prod$b(?v0), fun_app$k(fun_app$l(pair$b, ?v1), ?v2)))
tff(axiom208,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$i'('fun_app$j'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
     => 'fun_app$a'('case_prod$b'(A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ (fun_app$e(fun_app$f(?v0, ?v1), ?v2) ⇒ fun_app$i(case_prod$c(?v0), fun_app$g(fun_app$h(pair$a, ?v1), ?v2)))
tff(axiom209,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( 'fun_app$e'('fun_app$f'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
     => 'fun_app$i'('case_prod$c'(A__questionmark_v0),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(?v0, ?v1), ?v2) ⇒ fun_app$o(case_prod$(?v0), pair$c(?v1, ?v2)))
tff(axiom210,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)
     => 'fun_app$o'('case_prod$'(A__questionmark_v0),'pair$c'(A__questionmark_v1,A__questionmark_v2)) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ (∀ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v2), ?v3)) ⇒ fun_app$a(fun_app$b(?v1, ?v2), ?v3)) ⇒ fun_app$v(case_prod$a(?v1), ?v0))
tff(axiom211,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$'] :
      ( ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3) )
         => 'fun_app$a'('fun_app$b'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$v'('case_prod$a'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ (∀ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((?v0 = fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) ⇒ fun_app$i(fun_app$j(?v1, ?v2), ?v3)) ⇒ fun_app$a(case_prod$b(?v1), ?v0))
tff(axiom212,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
          ( ( A__questionmark_v0 = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3) )
         => 'fun_app$i'('fun_app$j'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$a'('case_prod$b'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ (∀ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) ⇒ fun_app$e(fun_app$f(?v1, ?v2), ?v3)) ⇒ fun_app$i(case_prod$c(?v1), ?v0))
tff(axiom213,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$'] :
      ( ! [A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3) )
         => 'fun_app$e'('fun_app$f'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$i'('case_prod$c'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Nat_nat_prod$ ?v1:Nat_nat_bool_fun_fun$ (∀ ?v2:Nat$ ?v3:Nat$ ((?v0 = pair$c(?v2, ?v3)) ⇒ fun_app$m(fun_app$n(?v1, ?v2), ?v3)) ⇒ fun_app$o(case_prod$(?v1), ?v0))
tff(axiom214,axiom,
    ! [A__questionmark_v0: 'Nat_nat_prod$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
          ( ( A__questionmark_v0 = 'pair$c'(A__questionmark_v2,A__questionmark_v3) )
         => 'fun_app$m'('fun_app$n'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$o'('case_prod$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$v(case_prod$a(?v0), fun_app$c(fun_app$d(pair$, ?v1), ?v2)) ⇒ fun_app$a(fun_app$b(?v0, ?v1), ?v2))
tff(axiom215,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$v'('case_prod$a'(A__questionmark_v0),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),A__questionmark_v2))
     => 'fun_app$a'('fun_app$b'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$a(case_prod$b(?v0), fun_app$k(fun_app$l(pair$b, ?v1), ?v2)) ⇒ fun_app$i(fun_app$j(?v0, ?v1), ?v2))
tff(axiom216,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$a'('case_prod$b'(A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),A__questionmark_v2))
     => 'fun_app$i'('fun_app$j'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ (fun_app$i(case_prod$c(?v0), fun_app$g(fun_app$h(pair$a, ?v1), ?v2)) ⇒ fun_app$e(fun_app$f(?v0, ?v1), ?v2))
tff(axiom217,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( 'fun_app$i'('case_prod$c'(A__questionmark_v0),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),A__questionmark_v2))
     => 'fun_app$e'('fun_app$f'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ (fun_app$o(case_prod$(?v0), pair$c(?v1, ?v2)) ⇒ fun_app$m(fun_app$n(?v0, ?v1), ?v2))
tff(axiom218,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$o'('case_prod$'(A__questionmark_v0),'pair$c'(A__questionmark_v1,A__questionmark_v2))
     => 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ((fun_app$v(case_prod$a(?v0), ?v1) ∧ ∀ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (((?v1 = fun_app$c(fun_app$d(pair$, ?v2), ?v3)) ∧ fun_app$a(fun_app$b(?v0, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom219,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ( 'fun_app$v'('case_prod$a'(A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
            ( ( ( A__questionmark_v1 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3) )
              & 'fun_app$a'('fun_app$b'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((fun_app$a(case_prod$b(?v0), ?v1) ∧ ∀ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (((?v1 = fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) ∧ fun_app$i(fun_app$j(?v0, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom220,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ( 'fun_app$a'('case_prod$b'(A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
            ( ( ( A__questionmark_v1 = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3) )
              & 'fun_app$i'('fun_app$j'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((fun_app$i(case_prod$c(?v0), ?v1) ∧ ∀ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (((?v1 = fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) ∧ fun_app$e(fun_app$f(?v0, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom221,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( 'fun_app$i'('case_prod$c'(A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
            ( ( ( A__questionmark_v1 = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3) )
              & 'fun_app$e'('fun_app$f'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat_nat_prod$ ((fun_app$o(case_prod$(?v0), ?v1) ∧ ∀ ?v2:Nat$ ?v3:Nat$ (((?v1 = pair$c(?v2, ?v3)) ∧ fun_app$m(fun_app$n(?v0, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom222,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat_nat_prod$'] :
      ( ( 'fun_app$o'('case_prod$'(A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
            ( ( ( A__questionmark_v1 = 'pair$c'(A__questionmark_v2,A__questionmark_v3) )
              & 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Bool_bool_fun$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_prod$ ((fun_app$p(?v0, fun_app$o(case_prod$(?v1), ?v2)) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (((?v2 = pair$c(?v3, ?v4)) ∧ fun_app$p(?v0, fun_app$m(fun_app$n(?v1, ?v3), ?v4))) ⇒ false)) ⇒ false)
tff(axiom223,axiom,
    ! [A__questionmark_v0: 'Bool_bool_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_prod$'] :
      ( ( 'fun_app$p'(A__questionmark_v0,def_4(A__questionmark_v1,A__questionmark_v2))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( ( ( A__questionmark_v2 = 'pair$c'(A__questionmark_v3,A__questionmark_v4) )
              & 'fun_app$p'(A__questionmark_v0,def_5(A__questionmark_v1,A__questionmark_v4,A__questionmark_v3)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat_nat_prod_bool_fun$ (case_prod$(uua$(?v0)) = ?v0)
tff(axiom224,axiom,
    ! [A__questionmark_v0: 'Nat_nat_prod_bool_fun$'] : ( 'case_prod$'('uua$'(A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat_nat_prod_bool_fun$ (∀ ?v2:Nat$ ?v3:Nat$ (fun_app$m(fun_app$n(?v0, ?v2), ?v3) = fun_app$o(?v1, pair$c(?v2, ?v3))) ⇒ (case_prod$(?v0) = ?v1))
tff(axiom225,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat_nat_prod_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
          ( 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v2),A__questionmark_v3)
        <=> 'fun_app$o'(A__questionmark_v1,'pair$c'(A__questionmark_v2,A__questionmark_v3)) )
     => ( 'case_prod$'(A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat_nat_bool_fun_fun$ (less_eq$e(?v0, ?v1) ⇒ less_eq$j(collect$a(case_prod$(?v0)), collect$a(case_prod$(?v1))))
tff(axiom226,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$'] :
      ( 'less_eq$e'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$j'('collect$a'('case_prod$'(A__questionmark_v0)),'collect$a'('case_prod$'(A__questionmark_v1))) ) ).

%% ∀ ?v0:Nat_nat_prod$ ((?v0 = ?v0) = fun_app$o(case_prod$(uub$), ?v0))
tff(axiom227,axiom,
    ! [A__questionmark_v0: 'Nat_nat_prod$'] :
      ( ( A__questionmark_v0 = A__questionmark_v0 )
    <=> 'fun_app$o'('case_prod$'('uub$'),A__questionmark_v0) ) ).

%% ∀ ?v0:Bool_bool_fun$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_prod$ (fun_app$p(?v0, fun_app$o(case_prod$(?v1), ?v2)) = fun_app$o(case_prod$(uuc$(?v0, ?v1)), ?v2))
tff(axiom228,axiom,
    ! [A__questionmark_v0: 'Bool_bool_fun$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_prod$'] :
      ( 'fun_app$p'(A__questionmark_v0,def_6(A__questionmark_v1,A__questionmark_v2))
    <=> 'fun_app$o'('case_prod$'('uuc$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = less_eq$c(uud$(?v0), uud$(?v1)))
tff(axiom229,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> 'less_eq$c'('uud$'(A__questionmark_v0),'uud$'(A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_bool_fun$ less_eq$(collect$(uue$(?v0, ?v1)), ?v0)
tff(axiom230,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_bool_fun$'] : 'less_eq$'('collect$'('uue$'(A__questionmark_v0,A__questionmark_v1)),A__questionmark_v0) ).

%% ∀ ?v0:A_run_bool_fun$ ?v1:A_run_bool_fun$ (collect$(uuf$(?v0, ?v1)) = fun_app$q(fun_app$r(inf$, collect$(?v0)), collect$(?v1)))
tff(axiom231,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v1: 'A_run_bool_fun$'] : ( 'collect$'('uuf$'(A__questionmark_v0,A__questionmark_v1)) = 'fun_app$q'('fun_app$r'('inf$','collect$'(A__questionmark_v0)),'collect$'(A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = collect$(fun_app$y(inf$c(uud$(?v0)), uud$(?v1))))
tff(axiom232,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'collect$'('fun_app$y'('inf$c'('uud$'(A__questionmark_v0)),'uud$'(A__questionmark_v1))) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_bool_fun$ (member$(?v0, fun_app$q(fun_app$r(inf$, ?v1), collect$(?v2))) = (member$(?v0, ?v1) ∧ fun_app$(?v2, ?v0)))
tff(axiom233,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_bool_fun$'] :
      ( 'member$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'collect$'(A__questionmark_v2)))
    <=> ( 'member$'(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$'(A__questionmark_v2,A__questionmark_v0) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = collect$(uug$(?v0, ?v1)))
tff(axiom234,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'collect$'('uug$'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ (fun_app$o(case_prod$(?v0), pair$c(?v1, ?v2)) = fun_app$m(fun_app$n(?v0, ?v1), ?v2))
tff(axiom235,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$o'('case_prod$'(A__questionmark_v0),'pair$c'(A__questionmark_v1,A__questionmark_v2))
    <=> 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(weaklyPrecedes$(?v2, ?v3), ?v4)), ?v5)))), fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v3, ?v1), tickCountLeq$(?v2, ?v1), case_prod$(less_eq$f)), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(weaklyPrecedes$(?v2, ?v3), ?v5)))))
tff(axiom236,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v3,A__questionmark_v1),'tickCountLeq$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (((fun_app$c(fun_app$d(pair$, ?v0), ?v1) = fun_app$c(fun_app$d(pair$, ?v2), ?v3)) ∧ (((?v0 = ?v2) ∧ (?v1 = ?v3)) ⇒ false)) ⇒ false)
tff(axiom237,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ( ( 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),A__questionmark_v1) = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3) )
        & ( ( ( A__questionmark_v0 = A__questionmark_v2 )
            & ( A__questionmark_v1 = A__questionmark_v3 ) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (((fun_app$k(fun_app$l(pair$b, ?v0), ?v1) = fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) ∧ (((?v0 = ?v2) ∧ (?v1 = ?v3)) ⇒ false)) ⇒ false)
tff(axiom238,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( ( 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v0),A__questionmark_v1) = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3) )
        & ( ( ( A__questionmark_v0 = A__questionmark_v2 )
            & ( A__questionmark_v1 = A__questionmark_v3 ) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (((fun_app$g(fun_app$h(pair$a, ?v0), ?v1) = fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) ∧ (((?v0 = ?v2) ∧ (?v1 = ?v3)) ⇒ false)) ⇒ false)
tff(axiom239,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( ( ( 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v0),A__questionmark_v1) = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3) )
        & ( ( ( A__questionmark_v0 = A__questionmark_v2 )
            & ( A__questionmark_v1 = A__questionmark_v3 ) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ fun_app$v(?v0, fun_app$c(fun_app$d(pair$, ?v2), ?v3)) ⇒ fun_app$v(?v0, ?v1))
tff(axiom240,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] : 'fun_app$v'(A__questionmark_v0,'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3))
     => 'fun_app$v'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (∀ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ fun_app$a(?v0, fun_app$k(fun_app$l(pair$b, ?v2), ?v3)) ⇒ fun_app$a(?v0, ?v1))
tff(axiom241,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] : 'fun_app$a'(A__questionmark_v0,'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3))
     => 'fun_app$a'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (∀ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ fun_app$i(?v0, fun_app$g(fun_app$h(pair$a, ?v2), ?v3)) ⇒ fun_app$i(?v0, ?v1))
tff(axiom242,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_bool_fun$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ! [A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] : 'fun_app$i'(A__questionmark_v0,'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3))
     => 'fun_app$i'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ∃ ?v1:A_constr_list$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (?v0 = fun_app$c(fun_app$d(pair$, ?v1), ?v2))
tff(axiom243,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
    ? [A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] : ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ∃ ?v1:Nat$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (?v0 = fun_app$k(fun_app$l(pair$b, ?v1), ?v2))
tff(axiom244,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
    ? [A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] : ( A__questionmark_v0 = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ∃ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ (?v0 = fun_app$g(fun_app$h(pair$a, ?v1), ?v2))
tff(axiom245,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
    ? [A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] : ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v1:A_constr_list$ ?v2:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v1), ?v2)) ⇒ false) ⇒ false)
tff(axiom246,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),A__questionmark_v2) )
         => $false )
     => $false ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (∀ ?v1:Nat$ ?v2:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((?v0 = fun_app$k(fun_app$l(pair$b, ?v1), ?v2)) ⇒ false) ⇒ false)
tff(axiom247,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ! [A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
          ( ( A__questionmark_v0 = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),A__questionmark_v2) )
         => $false )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (∀ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, ?v1), ?v2)) ⇒ false) ⇒ false)
tff(axiom248,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ! [A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),A__questionmark_v2) )
         => $false )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∃ ?v2:Nat$ ((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v2)) ∧ fun_app$m(?v1, ?v2)) = (fun_app$m(?v1, ?v0) ∨ ∃ ?v2:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) ≤ fun_app$u(of_nat$, ?v2)) ∧ fun_app$m(?v1, ?v2))))
tff(axiom249,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ? [A__questionmark_v2: 'Nat$'] :
          ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v2))
          & 'fun_app$m'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$m'(A__questionmark_v1,A__questionmark_v0)
        | ? [A__questionmark_v2: 'Nat$'] :
            ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),'fun_app$u'('of_nat$',A__questionmark_v2))
            & 'fun_app$m'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_bool_fun$ (∀ ?v2:Nat$ ((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v2)) ⇒ fun_app$m(?v1, ?v2)) = (fun_app$m(?v1, ?v0) ∧ ∀ ?v2:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) ≤ fun_app$u(of_nat$, ?v2)) ⇒ fun_app$m(?v1, ?v2))))
tff(axiom250,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_bool_fun$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v2))
         => 'fun_app$m'(A__questionmark_v1,A__questionmark_v2) )
    <=> ( 'fun_app$m'(A__questionmark_v1,A__questionmark_v0)
        & ! [A__questionmark_v2: 'Nat$'] :
            ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),'fun_app$u'('of_nat$',A__questionmark_v2))
           => 'fun_app$m'(A__questionmark_v1,A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list_a_TESL_atomic_list_prod$ fun_app$v(?v0, fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), ?v4))) ⇒ fun_app$v(?v0, ?v1))
tff(axiom251,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] : 'fun_app$v'(A__questionmark_v0,'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),A__questionmark_v4)))
     => 'fun_app$v'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (∀ ?v2:Nat$ ?v3:A_TESL_atomic_list$ ?v4:A_TESL_atomic_list$ fun_app$a(?v0, fun_app$k(fun_app$l(pair$b, ?v2), fun_app$g(fun_app$h(pair$a, ?v3), ?v4))) ⇒ fun_app$a(?v0, ?v1))
tff(axiom252,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_bool_fun$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_TESL_atomic_list$'] : 'fun_app$a'(A__questionmark_v0,'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),A__questionmark_v4)))
     => 'fun_app$a'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v1:A_constr_list$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v1), fun_app$k(fun_app$l(pair$b, ?v2), ?v3))) ⇒ false) ⇒ false)
tff(axiom253,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v1),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3)) )
         => $false )
     => $false ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (∀ ?v1:Nat$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ((?v0 = fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3))) ⇒ false) ⇒ false)
tff(axiom254,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ! [A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)) )
         => $false )
     => $false ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (∀ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ fun_app$v(?v0, fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))) ⇒ fun_app$v(?v0, ?v1))
tff(axiom255,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_bool_fun$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'fun_app$v'(A__questionmark_v0,'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5))))
     => 'fun_app$v'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) ≤ (fun_app$u(of_nat$, ?v1) + 1)) = (fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)))
tff(axiom256,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))
    <=> $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(weaklyPrecedes$(?v2, ?v3), ?v4)), ?v5)))) = heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v3, ?v1), tickCountLeq$(?v2, ?v1), case_prod$(less_eq$f)), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(weaklyPrecedes$(?v2, ?v3), ?v5))))))
tff(axiom257,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))) = 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v3,A__questionmark_v1),'tickCountLeq$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ) ).

%% ∀ ?v0:A_constr$ ?v1:A_constr_list$ less_eq$(symbolic_run_interpretation$(cons$a(?v0, ?v1)), symbolic_run_interpretation$(?v1))
tff(axiom258,axiom,
    ! [A__questionmark_v0: 'A_constr$',A__questionmark_v1: 'A_constr_list$'] : 'less_eq$'('symbolic_run_interpretation$'('cons$a'(A__questionmark_v0,A__questionmark_v1)),'symbolic_run_interpretation$'(A__questionmark_v1)) ).

%% ∀ ?v0:Cnt_expr$ ?v1:Cnt_expr$ ?v2:Nat_nat_prod_bool_fun$ ?v3:Cnt_expr$ ?v4:Cnt_expr$ ?v5:Nat_nat_prod_bool_fun$ ((tickCntArith$(?v0, ?v1, ?v2) = tickCntArith$(?v3, ?v4, ?v5)) = ((?v0 = ?v3) ∧ ((?v1 = ?v4) ∧ (?v2 = ?v5))))
tff(axiom259,axiom,
    ! [A__questionmark_v0: 'Cnt_expr$',A__questionmark_v1: 'Cnt_expr$',A__questionmark_v2: 'Nat_nat_prod_bool_fun$',A__questionmark_v3: 'Cnt_expr$',A__questionmark_v4: 'Cnt_expr$',A__questionmark_v5: 'Nat_nat_prod_bool_fun$'] :
      ( ( 'tickCntArith$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) = 'tickCntArith$'(A__questionmark_v3,A__questionmark_v4,A__questionmark_v5) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v3 )
        & ( A__questionmark_v1 = A__questionmark_v4 )
        & ( A__questionmark_v2 = A__questionmark_v5 ) ) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Clock$ ?v3:Nat$ ((tickCountLeq$(?v0, ?v1) = tickCountLeq$(?v2, ?v3)) = ((?v0 = ?v2) ∧ (fun_app$u(of_nat$, ?v1) = fun_app$u(of_nat$, ?v3))))
tff(axiom260,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Nat$'] :
      ( ( 'tickCountLeq$'(A__questionmark_v0,A__questionmark_v1) = 'tickCountLeq$'(A__questionmark_v2,A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( 'fun_app$u'('of_nat$',A__questionmark_v1) = 'fun_app$u'('of_nat$',A__questionmark_v3) ) ) ) ).

%% ∀ ?v0:Nat_a_run_set_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ less_eq$(fun_app$s(?v0, ?v3), fun_app$s(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ less_eq$(fun_app$s(?v0, ?v1), fun_app$s(?v0, ?v2)))
tff(axiom261,axiom,
    ! [A__questionmark_v0: 'Nat_a_run_set_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'less_eq$'('fun_app$s'(A__questionmark_v0,A__questionmark_v3),'fun_app$s'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => 'less_eq$'('fun_app$s'(A__questionmark_v0,A__questionmark_v1),'fun_app$s'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_nat_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v0, ?v3)), fun_app$aa(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v0, ?v1)), fun_app$aa(?v0, ?v2)))
tff(axiom262,axiom,
    ! [A__questionmark_v0: 'Nat_nat_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v0,A__questionmark_v3)),'fun_app$aa'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v0,A__questionmark_v1)),'fun_app$aa'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$u(?v0, ?v3) ≤ fun_app$u(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ (fun_app$u(?v0, ?v1) ≤ fun_app$u(?v0, ?v2)))
tff(axiom263,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$u'(A__questionmark_v0,A__questionmark_v3),'fun_app$u'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$u'(A__questionmark_v0,A__questionmark_v1),'fun_app$u'(A__questionmark_v0,A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat_a_run_set_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ less_eq$(fun_app$s(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1))), fun_app$s(?v0, ?v3)) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ less_eq$(fun_app$s(?v0, ?v2), fun_app$s(?v0, ?v1)))
tff(axiom264,axiom,
    ! [A__questionmark_v0: 'Nat_a_run_set_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'less_eq$'('fun_app$s'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))),'fun_app$s'(A__questionmark_v0,A__questionmark_v3))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => 'less_eq$'('fun_app$s'(A__questionmark_v0,A__questionmark_v2),'fun_app$s'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_nat_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))), fun_app$aa(?v0, ?v3)) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v0, ?v2)), fun_app$aa(?v0, ?v1)))
tff(axiom265,axiom,
    ! [A__questionmark_v0: 'Nat_nat_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1)))),'fun_app$aa'(A__questionmark_v0,A__questionmark_v3))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v0,A__questionmark_v2)),'fun_app$aa'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_int_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ (fun_app$u(?v0, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1))) ≤ fun_app$u(?v0, ?v3)) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ (fun_app$u(?v0, ?v2) ≤ fun_app$u(?v0, ?v1)))
tff(axiom266,axiom,
    ! [A__questionmark_v0: 'Nat_int_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$'] : $lesseq('fun_app$u'(A__questionmark_v0,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))),'fun_app$u'(A__questionmark_v0,A__questionmark_v3))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$u'(A__questionmark_v0,A__questionmark_v2),'fun_app$u'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) = (fun_app$u(of_nat$, ?v1) + 1)) = (fun_app$u(of_nat$, ?v0) = fun_app$u(of_nat$, ?v1)))
tff(axiom267,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$u'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$u'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$u'('of_nat$',A__questionmark_v0) = 'fun_app$u'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) = (fun_app$u(of_nat$, ?v1) + 1)) = (fun_app$u(of_nat$, ?v0) = fun_app$u(of_nat$, ?v1)))
tff(axiom268,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$u'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$u'('of_nat$',A__questionmark_v1),1) )
    <=> ( 'fun_app$u'('of_nat$',A__questionmark_v0) = 'fun_app$u'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ¬(fun_app$u(of_nat$, ?v0) = (fun_app$u(of_nat$, ?v0) + 1))
tff(axiom269,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$u'('of_nat$',A__questionmark_v0) != $sum('fun_app$u'('of_nat$',A__questionmark_v0),1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) = (fun_app$u(of_nat$, ?v1) + 1)) ⇒ (fun_app$u(of_nat$, ?v0) = fun_app$u(of_nat$, ?v1)))
tff(axiom270,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $sum('fun_app$u'('of_nat$',A__questionmark_v0),1) = $sum('fun_app$u'('of_nat$',A__questionmark_v1),1) )
     => ( 'fun_app$u'('of_nat$',A__questionmark_v0) = 'fun_app$u'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(?v0, ?v1) ∧ ∀ ?v3:Nat$ (fun_app$m(?v0, ?v3) ⇒ (fun_app$u(of_nat$, ?v3) ≤ fun_app$u(of_nat$, ?v2)))) ⇒ ∃ ?v3:Nat$ (fun_app$m(?v0, ?v3) ∧ ∀ ?v4:Nat$ (fun_app$m(?v0, ?v4) ⇒ (fun_app$u(of_nat$, ?v4) ≤ fun_app$u(of_nat$, ?v3)))))
tff(axiom271,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'(A__questionmark_v0,A__questionmark_v1)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( 'fun_app$m'(A__questionmark_v0,A__questionmark_v3)
           => $lesseq('fun_app$u'('of_nat$',A__questionmark_v3),'fun_app$u'('of_nat$',A__questionmark_v2)) ) )
     => ? [A__questionmark_v3: 'Nat$'] :
          ( 'fun_app$m'(A__questionmark_v0,A__questionmark_v3)
          & ! [A__questionmark_v4: 'Nat$'] :
              ( 'fun_app$m'(A__questionmark_v0,A__questionmark_v4)
             => $lesseq('fun_app$u'('of_nat$',A__questionmark_v4),'fun_app$u'('of_nat$',A__questionmark_v3)) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∨ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v0)))
tff(axiom272,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
      | $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v0))) ⇒ (fun_app$u(of_nat$, ?v0) = fun_app$u(of_nat$, ?v1)))
tff(axiom273,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v0)) )
     => ( 'fun_app$u'('of_nat$',A__questionmark_v0) = 'fun_app$u'('of_nat$',A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$u(of_nat$, ?v0) = fun_app$u(of_nat$, ?v1)) ⇒ (fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)))
tff(axiom274,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$u'('of_nat$',A__questionmark_v0) = 'fun_app$u'('of_nat$',A__questionmark_v1) )
     => $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∧ (fun_app$u(of_nat$, ?v1) ≤ fun_app$u(of_nat$, ?v2))) ⇒ (fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v2)))
tff(axiom275,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
        & $lesseq('fun_app$u'('of_nat$',A__questionmark_v1),'fun_app$u'('of_nat$',A__questionmark_v2)) )
     => $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ (fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v0))
tff(axiom276,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_bool_fun_fun$ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∧ (∀ ?v3:Nat$ fun_app$m(fun_app$n(?v2, ?v3), ?v3) ∧ (∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ ((fun_app$m(fun_app$n(?v2, ?v3), ?v4) ∧ fun_app$m(fun_app$n(?v2, ?v4), ?v5)) ⇒ fun_app$m(fun_app$n(?v2, ?v3), ?v5)) ∧ ∀ ?v3:Nat$ fun_app$m(fun_app$n(?v2, ?v3), fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))))) ⇒ fun_app$m(fun_app$n(?v2, ?v0), ?v1))
tff(axiom277,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$'] :
      ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v3)
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)
              & 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v4),A__questionmark_v5) )
           => 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5) )
        & ! [A__questionmark_v3: 'Nat$'] : 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v3),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))) )
     => 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_bool_fun$ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∧ (fun_app$m(?v2, ?v0) ∧ ∀ ?v3:Nat$ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v3)) ∧ fun_app$m(?v2, ?v3)) ⇒ fun_app$m(?v2, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))))) ⇒ fun_app$m(?v2, ?v1))
tff(axiom278,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_bool_fun$'] :
      ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
        & 'fun_app$m'(A__questionmark_v2,A__questionmark_v0)
        & ! [A__questionmark_v3: 'Nat$'] :
            ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v3))
              & 'fun_app$m'(A__questionmark_v2,A__questionmark_v3) )
           => 'fun_app$m'(A__questionmark_v2,'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))) ) )
     => 'fun_app$m'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_bool_fun$ ?v1:Nat$ (∀ ?v2:Nat$ (∀ ?v3:Nat$ (((fun_app$u(of_nat$, ?v3) + 1) ≤ fun_app$u(of_nat$, ?v2)) ⇒ fun_app$m(?v0, ?v3)) ⇒ fun_app$m(?v0, ?v2)) ⇒ fun_app$m(?v0, ?v1))
tff(axiom279,axiom,
    ! [A__questionmark_v0: 'Nat_bool_fun$',A__questionmark_v1: 'Nat$'] :
      ( ! [A__questionmark_v2: 'Nat$'] :
          ( ! [A__questionmark_v3: 'Nat$'] :
              ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v3),1),'fun_app$u'('of_nat$',A__questionmark_v2))
             => 'fun_app$m'(A__questionmark_v0,A__questionmark_v3) )
         => 'fun_app$m'(A__questionmark_v0,A__questionmark_v2) )
     => 'fun_app$m'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬(fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) = ((fun_app$u(of_nat$, ?v1) + 1) ≤ fun_app$u(of_nat$, ?v0)))
tff(axiom280,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
    <=> $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v1),1),'fun_app$u'('of_nat$',A__questionmark_v0)) ) ).

%% ∀ ?v0:Nat$ ¬((fun_app$u(of_nat$, ?v0) + 1) ≤ fun_app$u(of_nat$, ?v0))
tff(axiom281,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ~ $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),'fun_app$u'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$u(of_nat$, ?v0) ≤ (fun_app$u(of_nat$, ?v1) + 1)) = ((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ∨ (fun_app$u(of_nat$, ?v0) = (fun_app$u(of_nat$, ?v1) + 1))))
tff(axiom282,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))
    <=> ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
        | ( 'fun_app$u'('of_nat$',A__questionmark_v0) = $sum('fun_app$u'('of_nat$',A__questionmark_v1),1) ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) ≤ fun_app$u(of_nat$, ?v1)) ⇒ ∃ ?v2:Nat$ (fun_app$u(of_nat$, ?v1) = (fun_app$u(of_nat$, ?v2) + 1)))
tff(axiom283,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),'fun_app$u'('of_nat$',A__questionmark_v1))
     => ? [A__questionmark_v2: 'Nat$'] : ( 'fun_app$u'('of_nat$',A__questionmark_v1) = $sum('fun_app$u'('of_nat$',A__questionmark_v2),1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ⇒ (fun_app$u(of_nat$, ?v0) ≤ (fun_app$u(of_nat$, ?v1) + 1)))
tff(axiom284,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),$sum('fun_app$u'('of_nat$',A__questionmark_v1),1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) ≤ (fun_app$u(of_nat$, ?v1) + 1)) ∧ (((fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)) ⇒ false) ∧ ((fun_app$u(of_nat$, ?v0) = (fun_app$u(of_nat$, ?v1) + 1)) ⇒ false))) ⇒ false)
tff(axiom285,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))
        & ( $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1))
         => $false )
        & ( ( 'fun_app$u'('of_nat$',A__questionmark_v0) = $sum('fun_app$u'('of_nat$',A__questionmark_v1),1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$u(of_nat$, ?v0) + 1) ≤ fun_app$u(of_nat$, ?v1)) ⇒ (fun_app$u(of_nat$, ?v0) ≤ fun_app$u(of_nat$, ?v1)))
tff(axiom286,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( $lesseq($sum('fun_app$u'('of_nat$',A__questionmark_v0),1),'fun_app$u'('of_nat$',A__questionmark_v1))
     => $lesseq('fun_app$u'('of_nat$',A__questionmark_v0),'fun_app$u'('of_nat$',A__questionmark_v1)) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v3)))) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, symbolic_run_interpretation$(?v0)), fun_app$s(tESL_interpretation_stepwise$(?v2), ?v1))), fun_app$s(tESL_interpretation_stepwise$(?v3), fun_app$t(nat$, (fun_app$u(of_nat$, ?v1) + 1)))))
tff(axiom287,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3)))) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','symbolic_run_interpretation$'(A__questionmark_v0)),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v2),A__questionmark_v1))),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v3),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v1),1)))) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_run_set$ (((heronConf_interpretation$(?v0) = ?v1) ∧ ∀ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))) ∧ (?v1 = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, symbolic_run_interpretation$(?v2)), fun_app$s(tESL_interpretation_stepwise$(?v4), ?v3))), fun_app$s(tESL_interpretation_stepwise$(?v5), fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1)))))) ⇒ false)) ⇒ false)
tff(axiom288,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_run_set$'] :
      ( ( ( 'heronConf_interpretation$'(A__questionmark_v0) = A__questionmark_v1 )
        & ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5))) )
              & ( A__questionmark_v1 = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','symbolic_run_interpretation$'(A__questionmark_v2)),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v4),A__questionmark_v3))),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v5),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1)))) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ (less_eq$a(uuh$(?v0), uuh$(?v1)) = less_eq$i(?v0, ?v1))
tff(axiom289,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( 'less_eq$a'('uuh$'(A__questionmark_v0),'uuh$'(A__questionmark_v1))
    <=> 'less_eq$i'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ (less_eq$d(uui$(?v0), uui$(?v1)) = less_eq$h(?v0, ?v1))
tff(axiom290,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( 'less_eq$d'('uui$'(A__questionmark_v0),'uui$'(A__questionmark_v1))
    <=> 'less_eq$h'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ (less_eq$b(uuj$(?v0), uuj$(?v1)) = less_eq$g(?v0, ?v1))
tff(axiom291,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( 'less_eq$b'('uuj$'(A__questionmark_v0),'uuj$'(A__questionmark_v1))
    <=> 'less_eq$g'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Clock$ ?v1:Clock$ ?v2:Clock$ ?v3:Clock$ ((weaklyPrecedes$(?v0, ?v1) = weaklyPrecedes$(?v2, ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom292,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Clock$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$'] :
      ( ( 'weaklyPrecedes$'(A__questionmark_v0,A__questionmark_v1) = 'weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (fun_app$v(operational_semantics_elim_inv$(?v0), ?v1) = fun_app$v(operational_semantics_elim$(?v1), ?v0))
tff(axiom293,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( 'fun_app$v'('operational_semantics_elim_inv$'(A__questionmark_v0),A__questionmark_v1)
    <=> 'fun_app$v'('operational_semantics_elim$'(A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ (fun_app$(fun_app$y(inf$c(uud$(?v0)), uud$(?v1)), ?v2) = member$(?v2, fun_app$q(fun_app$r(inf$, ?v0), ?v1)))
tff(axiom294,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( 'fun_app$'('fun_app$y'('inf$c'('uud$'(A__questionmark_v0)),'uud$'(A__questionmark_v1)),A__questionmark_v2)
    <=> 'member$'(A__questionmark_v2,'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ less_eq$(?v0, ?v0)
tff(axiom295,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v0)
tff(axiom296,axiom,
    ! [A__questionmark_v0: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Int (?v0 ≤ ?v0)
tff(axiom297,axiom,
    ! [A__questionmark_v0: $int] : $lesseq(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ less_eq$(?v0, ?v0)
tff(axiom298,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v0)
tff(axiom299,axiom,
    ! [A__questionmark_v0: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v0) ).

%% ∀ ?v0:Int (?v0 ≤ ?v0)
tff(axiom300,axiom,
    ! [A__questionmark_v0: $int] : $lesseq(A__questionmark_v0,A__questionmark_v0) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (¬fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0) ∧ ¬(?v1 = ?v0)))
tff(axiom301,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ~ 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0)
        & ( A__questionmark_v1 != A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int (¬(?v0 ≤ ?v1) = ((?v1 ≤ ?v0) ∧ ¬(?v1 = ?v0)))
tff(axiom302,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ~ $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( $lesseq(A__questionmark_v1,A__questionmark_v0)
        & ( A__questionmark_v1 != A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ false) ∧ (((fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2)) ⇒ false) ∧ (((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1)) ⇒ false) ∧ (((fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)) ⇒ false) ∧ (((fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v0)) ⇒ false) ∧ ((fun_app$m(fun_app$n(less_eq$f, ?v2), ?v0) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1)) ⇒ false)))))) ⇒ false)
tff(axiom303,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
         => $false )
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) )
         => $false )
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1) )
         => $false )
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) )
         => $false )
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v0) )
         => $false )
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v0)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v2)) ⇒ false) ∧ ((((?v1 ≤ ?v0) ∧ (?v0 ≤ ?v2)) ⇒ false) ∧ ((((?v0 ≤ ?v2) ∧ (?v2 ≤ ?v1)) ⇒ false) ∧ ((((?v2 ≤ ?v1) ∧ (?v1 ≤ ?v0)) ⇒ false) ∧ ((((?v1 ≤ ?v2) ∧ (?v2 ≤ ?v0)) ⇒ false) ∧ (((?v2 ≤ ?v0) ∧ (?v0 ≤ ?v1)) ⇒ false)))))) ⇒ false)
tff(axiom304,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
            & $lesseq(A__questionmark_v1,A__questionmark_v2) )
         => $false )
        & ( ( $lesseq(A__questionmark_v1,A__questionmark_v0)
            & $lesseq(A__questionmark_v0,A__questionmark_v2) )
         => $false )
        & ( ( $lesseq(A__questionmark_v0,A__questionmark_v2)
            & $lesseq(A__questionmark_v2,A__questionmark_v1) )
         => $false )
        & ( ( $lesseq(A__questionmark_v2,A__questionmark_v1)
            & $lesseq(A__questionmark_v1,A__questionmark_v0) )
         => $false )
        & ( ( $lesseq(A__questionmark_v1,A__questionmark_v2)
            & $lesseq(A__questionmark_v2,A__questionmark_v0) )
         => $false )
        & ( ( $lesseq(A__questionmark_v2,A__questionmark_v0)
            & $lesseq(A__questionmark_v0,A__questionmark_v1) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)))
tff(axiom305,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = ?v1) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)))
tff(axiom306,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = ?v1) = ((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v0)))
tff(axiom307,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (((?v0 = ?v1) ∧ less_eq$(?v1, ?v2)) ⇒ less_eq$(?v0, ?v2))
tff(axiom308,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (((?v0 = ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2))
tff(axiom309,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 = ?v1) ∧ (?v1 ≤ ?v2)) ⇒ (?v0 ≤ ?v2))
tff(axiom310,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ( A__questionmark_v0 = A__questionmark_v1 )
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ (?v1 = ?v2)) ⇒ less_eq$(?v0, ?v2))
tff(axiom311,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ (?v1 = ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2))
tff(axiom312,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v1 = ?v2)) ⇒ (?v0 ≤ ?v2))
tff(axiom313,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( A__questionmark_v1 = A__questionmark_v2 ) )
     => $lesseq(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)) ⇒ (?v0 = ?v1))
tff(axiom314,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)) ⇒ (?v0 = ?v1))
tff(axiom315,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v0)) ⇒ (?v0 = ?v1))
tff(axiom316,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v2)) ⇒ less_eq$(?v0, ?v2))
tff(axiom317,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2))
tff(axiom318,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v2)) ⇒ (?v0 ≤ ?v2))
tff(axiom319,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v2)) ⇒ less_eq$(?v0, ?v2))
tff(axiom320,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2))
tff(axiom321,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v2)) ⇒ (?v0 ≤ ?v2))
tff(axiom322,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) )
     => $lesseq(A__questionmark_v0,A__questionmark_v2) ) ).

%% ∀ ?v0:Nat_nat_bool_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v3), ?v4) ⇒ fun_app$m(fun_app$n(?v0, ?v3), ?v4)) ∧ ∀ ?v3:Nat$ ?v4:Nat$ (fun_app$m(fun_app$n(?v0, ?v4), ?v3) ⇒ fun_app$m(fun_app$n(?v0, ?v3), ?v4))) ⇒ fun_app$m(fun_app$n(?v0, ?v1), ?v2))
tff(axiom323,axiom,
    ! [A__questionmark_v0: 'Nat_nat_bool_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v3),A__questionmark_v4)
           => 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$m'('fun_app$n'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:Int_int_bool_fun_fun$ ?v1:Int ?v2:Int ((∀ ?v3:Int ?v4:Int ((?v3 ≤ ?v4) ⇒ fun_app$ae(fun_app$af(?v0, ?v3), ?v4)) ∧ ∀ ?v3:Int ?v4:Int (fun_app$ae(fun_app$af(?v0, ?v4), ?v3) ⇒ fun_app$ae(fun_app$af(?v0, ?v3), ?v4))) ⇒ fun_app$ae(fun_app$af(?v0, ?v1), ?v2))
tff(axiom324,axiom,
    ! [A__questionmark_v0: 'Int_int_bool_fun_fun$',A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ! [A__questionmark_v3: $int,A__questionmark_v4: $int] :
            ( $lesseq(A__questionmark_v3,A__questionmark_v4)
           => 'fun_app$ae'('fun_app$af'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) )
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int] :
            ( 'fun_app$ae'('fun_app$af'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)
           => 'fun_app$ae'('fun_app$af'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4) ) )
     => 'fun_app$ae'('fun_app$af'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) = (less_eq$(?v1, ?v0) ∧ less_eq$(?v0, ?v1)))
tff(axiom325,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'less_eq$'(A__questionmark_v1,A__questionmark_v0)
        & 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = ?v1) = (fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0) ∧ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1)))
tff(axiom326,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = ?v1) = ((?v1 ≤ ?v0) ∧ (?v0 ≤ ?v1)))
tff(axiom327,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( $lesseq(A__questionmark_v1,A__questionmark_v0)
        & $lesseq(A__questionmark_v0,A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)) ⇒ (?v1 = ?v0))
tff(axiom328,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v1 = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)) ⇒ (?v1 = ?v0))
tff(axiom329,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) )
     => ( A__questionmark_v1 = A__questionmark_v0 ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v0)) ⇒ (?v1 = ?v0))
tff(axiom330,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v1 = A__questionmark_v0 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v0)) ⇒ less_eq$(?v2, ?v1))
tff(axiom331,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v0) )
     => 'less_eq$'(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v0)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1))
tff(axiom332,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v0) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v0)) ⇒ (?v2 ≤ ?v1))
tff(axiom333,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v0) )
     => $lesseq(A__questionmark_v2,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)) ⇒ (?v0 = ?v1))
tff(axiom334,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)) ⇒ (?v0 = ?v1))
tff(axiom335,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v0)) ⇒ (?v0 = ?v1))
tff(axiom336,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v0) )
     => ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) = (less_eq$(?v0, ?v1) ∧ less_eq$(?v1, ?v0)))
tff(axiom337,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = ?v1) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0)))
tff(axiom338,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = ?v1) = ((?v0 ≤ ?v1) ∧ (?v1 ≤ ?v0)))
tff(axiom339,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v1,A__questionmark_v0) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set_a_run_set_fun$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, fun_app$q(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ less_eq$(fun_app$q(?v1, ?v4), fun_app$q(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$q(?v1, ?v3)))
tff(axiom340,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set_a_run_set_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$q'(A__questionmark_v1,A__questionmark_v2))
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$q'(A__questionmark_v1,A__questionmark_v4),'fun_app$q'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:Nat_a_run_set_fun$ ?v2:Nat$ ?v3:Nat$ ((less_eq$(?v0, fun_app$s(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ less_eq$(fun_app$s(?v1, ?v4), fun_app$s(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$s(?v1, ?v3)))
tff(axiom341,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'Nat_a_run_set_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$s'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'less_eq$'('fun_app$s'(A__questionmark_v1,A__questionmark_v4),'fun_app$s'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$s'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:Int_a_run_set_fun$ ?v2:Int ?v3:Int ((less_eq$(?v0, fun_app$ag(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ less_eq$(fun_app$ag(?v1, ?v4), fun_app$ag(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$ag(?v1, ?v3)))
tff(axiom342,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'Int_a_run_set_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$ag'(A__questionmark_v1,A__questionmark_v2))
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$ag'(A__questionmark_v1,A__questionmark_v4),'fun_app$ag'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$ag'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:A_run_set_nat_fun$ ?v2:A_run_set$ ?v3:A_run_set$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$ah(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v1, ?v4)), fun_app$ah(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$ah(?v1, ?v3)))
tff(axiom343,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_run_set_nat_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$ah'(A__questionmark_v1,A__questionmark_v2))
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v1,A__questionmark_v4)),'fun_app$ah'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$ah'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_nat_fun$ ?v2:Nat$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v1, ?v4)), fun_app$aa(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(?v1, ?v3)))
tff(axiom344,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_nat_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v1,A__questionmark_v4)),'fun_app$aa'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Int_nat_fun$ ?v2:Int ?v3:Int ((fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$t(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v1, ?v4)), fun_app$t(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$t(?v1, ?v3)))
tff(axiom345,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Int_nat_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$t'(A__questionmark_v1,A__questionmark_v2))
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v1,A__questionmark_v4)),'fun_app$t'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$t'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:A_run_set_int_fun$ ?v2:A_run_set$ ?v3:A_run_set$ (((?v0 ≤ fun_app$ai(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ (fun_app$ai(?v1, ?v4) ≤ fun_app$ai(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$ai(?v1, ?v3)))
tff(axiom346,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'A_run_set_int_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( $lesseq(A__questionmark_v0,'fun_app$ai'(A__questionmark_v1,A__questionmark_v2))
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ai'(A__questionmark_v1,A__questionmark_v4),'fun_app$ai'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$ai'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Nat_int_fun$ ?v2:Nat$ ?v3:Nat$ (((?v0 ≤ fun_app$u(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ (fun_app$u(?v1, ?v4) ≤ fun_app$u(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$u(?v1, ?v3)))
tff(axiom347,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat_int_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( $lesseq(A__questionmark_v0,'fun_app$u'(A__questionmark_v1,A__questionmark_v2))
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => $lesseq('fun_app$u'(A__questionmark_v1,A__questionmark_v4),'fun_app$u'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$u'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int_int_fun$ ?v2:Int ?v3:Int (((?v0 ≤ fun_app$ac(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ (fun_app$ac(?v1, ?v4) ≤ fun_app$ac(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$ac(?v1, ?v3)))
tff(axiom348,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_int_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,'fun_app$ac'(A__questionmark_v1,A__questionmark_v2))
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ac'(A__questionmark_v1,A__questionmark_v4),'fun_app$ac'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$ac'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_a_run_set_fun$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ (less_eq$(fun_app$q(?v2, ?v1), ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ less_eq$(fun_app$q(?v2, ?v4), fun_app$q(?v2, ?v5))))) ⇒ less_eq$(fun_app$q(?v2, ?v0), ?v3))
tff(axiom349,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'('fun_app$q'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$q'(A__questionmark_v2,A__questionmark_v4),'fun_app$q'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$q'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_nat_fun$ ?v3:Nat$ ((less_eq$(?v0, ?v1) ∧ (fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v2, ?v1)), ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v2, ?v4)), fun_app$ah(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v2, ?v0)), ?v3))
tff(axiom350,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v2,A__questionmark_v4)),'fun_app$ah'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_int_fun$ ?v3:Int ((less_eq$(?v0, ?v1) ∧ ((fun_app$ai(?v2, ?v1) ≤ ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ (fun_app$ai(?v2, ?v4) ≤ fun_app$ai(?v2, ?v5))))) ⇒ (fun_app$ai(?v2, ?v0) ≤ ?v3))
tff(axiom351,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_int_fun$',A__questionmark_v3: $int] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & $lesseq('fun_app$ai'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ai'(A__questionmark_v2,A__questionmark_v4),'fun_app$ai'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$ai'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_a_run_set_fun$ ?v3:A_run_set$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ (less_eq$(fun_app$s(?v2, ?v1), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ less_eq$(fun_app$s(?v2, ?v4), fun_app$s(?v2, ?v5))))) ⇒ less_eq$(fun_app$s(?v2, ?v0), ?v3))
tff(axiom352,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'less_eq$'('fun_app$s'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'less_eq$'('fun_app$s'(A__questionmark_v2,A__questionmark_v4),'fun_app$s'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$s'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_fun$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ (fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v2, ?v4)), fun_app$aa(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v2, ?v0)), ?v3))
tff(axiom353,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v2,A__questionmark_v4)),'fun_app$aa'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_int_fun$ ?v3:Int ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((fun_app$u(?v2, ?v1) ≤ ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ (fun_app$u(?v2, ?v4) ≤ fun_app$u(?v2, ?v5))))) ⇒ (fun_app$u(?v2, ?v0) ≤ ?v3))
tff(axiom354,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_int_fun$',A__questionmark_v3: $int] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & $lesseq('fun_app$u'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => $lesseq('fun_app$u'(A__questionmark_v2,A__questionmark_v4),'fun_app$u'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$u'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_a_run_set_fun$ ?v3:A_run_set$ (((?v0 ≤ ?v1) ∧ (less_eq$(fun_app$ag(?v2, ?v1), ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ less_eq$(fun_app$ag(?v2, ?v4), fun_app$ag(?v2, ?v5))))) ⇒ less_eq$(fun_app$ag(?v2, ?v0), ?v3))
tff(axiom355,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'('fun_app$ag'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$ag'(A__questionmark_v2,A__questionmark_v4),'fun_app$ag'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$ag'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_nat_fun$ ?v3:Nat$ (((?v0 ≤ ?v1) ∧ (fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v2, ?v1)), ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v2, ?v4)), fun_app$t(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v2, ?v0)), ?v3))
tff(axiom356,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v2,A__questionmark_v1)),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v2,A__questionmark_v4)),'fun_app$t'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_int_fun$ ?v3:Int (((?v0 ≤ ?v1) ∧ ((fun_app$ac(?v2, ?v1) ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ (fun_app$ac(?v2, ?v4) ≤ fun_app$ac(?v2, ?v5))))) ⇒ (fun_app$ac(?v2, ?v0) ≤ ?v3))
tff(axiom357,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_int_fun$',A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq('fun_app$ac'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ac'(A__questionmark_v2,A__questionmark_v4),'fun_app$ac'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$ac'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = ?v1) ⇒ less_eq$(?v0, ?v1))
tff(axiom358,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1))
tff(axiom359,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = ?v1) ⇒ (?v0 ≤ ?v1))
tff(axiom360,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = A__questionmark_v1 )
     => $lesseq(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∨ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0))
tff(axiom361,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
      | 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ∨ (?v1 ≤ ?v0))
tff(axiom362,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
      | $lesseq(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set_a_run_set_fun$ ?v2:A_run_set$ ?v3:A_run_set$ (((?v0 = fun_app$q(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ less_eq$(fun_app$q(?v1, ?v4), fun_app$q(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$q(?v1, ?v3)))
tff(axiom363,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set_a_run_set_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$q'(A__questionmark_v1,A__questionmark_v2) )
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$q'(A__questionmark_v1,A__questionmark_v4),'fun_app$q'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:A_run_set_nat_fun$ ?v2:A_run_set$ ?v3:A_run_set$ (((?v0 = fun_app$ah(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v1, ?v4)), fun_app$ah(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$ah(?v1, ?v3)))
tff(axiom364,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_run_set_nat_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$ah'(A__questionmark_v1,A__questionmark_v2) )
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v1,A__questionmark_v4)),'fun_app$ah'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$ah'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:A_run_set_int_fun$ ?v2:A_run_set$ ?v3:A_run_set$ (((?v0 = fun_app$ai(?v1, ?v2)) ∧ (less_eq$(?v2, ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ (fun_app$ai(?v1, ?v4) ≤ fun_app$ai(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$ai(?v1, ?v3)))
tff(axiom365,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'A_run_set_int_fun$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$ai'(A__questionmark_v1,A__questionmark_v2) )
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ai'(A__questionmark_v1,A__questionmark_v4),'fun_app$ai'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$ai'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:Nat_a_run_set_fun$ ?v2:Nat$ ?v3:Nat$ (((?v0 = fun_app$s(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ less_eq$(fun_app$s(?v1, ?v4), fun_app$s(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$s(?v1, ?v3)))
tff(axiom366,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'Nat_a_run_set_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$s'(A__questionmark_v1,A__questionmark_v2) )
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'less_eq$'('fun_app$s'(A__questionmark_v1,A__questionmark_v4),'fun_app$s'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$s'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat_nat_fun$ ?v2:Nat$ ?v3:Nat$ (((?v0 = fun_app$aa(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v1, ?v4)), fun_app$aa(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(?v1, ?v3)))
tff(axiom367,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat_nat_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$aa'(A__questionmark_v1,A__questionmark_v2) )
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v1,A__questionmark_v4)),'fun_app$aa'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Nat_int_fun$ ?v2:Nat$ ?v3:Nat$ (((?v0 = fun_app$u(?v1, ?v2)) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ (fun_app$u(?v1, ?v4) ≤ fun_app$u(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$u(?v1, ?v3)))
tff(axiom368,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Nat_int_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( ( A__questionmark_v0 = 'fun_app$u'(A__questionmark_v1,A__questionmark_v2) )
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3)
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => $lesseq('fun_app$u'(A__questionmark_v1,A__questionmark_v4),'fun_app$u'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$u'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:Int_a_run_set_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$ag(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ less_eq$(fun_app$ag(?v1, ?v4), fun_app$ag(?v1, ?v5))))) ⇒ less_eq$(?v0, fun_app$ag(?v1, ?v3)))
tff(axiom369,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'Int_a_run_set_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$ag'(A__questionmark_v1,A__questionmark_v2) )
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$ag'(A__questionmark_v1,A__questionmark_v4),'fun_app$ag'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'less_eq$'(A__questionmark_v0,'fun_app$ag'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Int_nat_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$t(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v1, ?v4)), fun_app$t(?v1, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$t(?v1, ?v3)))
tff(axiom370,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Int_nat_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$t'(A__questionmark_v1,A__questionmark_v2) )
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v1,A__questionmark_v4)),'fun_app$t'(A__questionmark_v1,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$t'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int_int_fun$ ?v2:Int ?v3:Int (((?v0 = fun_app$ac(?v1, ?v2)) ∧ ((?v2 ≤ ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ (fun_app$ac(?v1, ?v4) ≤ fun_app$ac(?v1, ?v5))))) ⇒ (?v0 ≤ fun_app$ac(?v1, ?v3)))
tff(axiom371,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: 'Int_int_fun$',A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( ( A__questionmark_v0 = 'fun_app$ac'(A__questionmark_v1,A__questionmark_v2) )
        & $lesseq(A__questionmark_v2,A__questionmark_v3)
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ac'(A__questionmark_v1,A__questionmark_v4),'fun_app$ac'(A__questionmark_v1,A__questionmark_v5)) ) )
     => $lesseq(A__questionmark_v0,'fun_app$ac'(A__questionmark_v1,A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_a_run_set_fun$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ ((fun_app$q(?v2, ?v1) = ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ less_eq$(fun_app$q(?v2, ?v4), fun_app$q(?v2, ?v5))))) ⇒ less_eq$(fun_app$q(?v2, ?v0), ?v3))
tff(axiom372,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$q'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$q'(A__questionmark_v2,A__questionmark_v4),'fun_app$q'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$q'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_nat_fun$ ?v3:Nat$ ((less_eq$(?v0, ?v1) ∧ ((fun_app$ah(?v2, ?v1) = ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v2, ?v4)), fun_app$ah(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$ah(?v2, ?v0)), ?v3))
tff(axiom373,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$ah'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v2,A__questionmark_v4)),'fun_app$ah'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$ah'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set_int_fun$ ?v3:Int ((less_eq$(?v0, ?v1) ∧ ((fun_app$ai(?v2, ?v1) = ?v3) ∧ ∀ ?v4:A_run_set$ ?v5:A_run_set$ (less_eq$(?v4, ?v5) ⇒ (fun_app$ai(?v2, ?v4) ≤ fun_app$ai(?v2, ?v5))))) ⇒ (fun_app$ai(?v2, ?v0) ≤ ?v3))
tff(axiom374,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set_int_fun$',A__questionmark_v3: $int] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$ai'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( 'less_eq$'(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ai'(A__questionmark_v2,A__questionmark_v4),'fun_app$ai'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$ai'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_a_run_set_fun$ ?v3:A_run_set$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((fun_app$s(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ less_eq$(fun_app$s(?v2, ?v4), fun_app$s(?v2, ?v5))))) ⇒ less_eq$(fun_app$s(?v2, ?v0), ?v3))
tff(axiom375,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( 'fun_app$s'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'less_eq$'('fun_app$s'(A__questionmark_v2,A__questionmark_v4),'fun_app$s'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$s'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_nat_fun$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((fun_app$aa(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v2, ?v4)), fun_app$aa(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(?v2, ?v0)), ?v3))
tff(axiom376,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( 'fun_app$aa'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v2,A__questionmark_v4)),'fun_app$aa'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat_int_fun$ ?v3:Int ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((fun_app$u(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Nat$ ?v5:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v4), ?v5) ⇒ (fun_app$u(?v2, ?v4) ≤ fun_app$u(?v2, ?v5))))) ⇒ (fun_app$u(?v2, ?v0) ≤ ?v3))
tff(axiom377,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat_int_fun$',A__questionmark_v3: $int] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( 'fun_app$u'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v5)
           => $lesseq('fun_app$u'(A__questionmark_v2,A__questionmark_v4),'fun_app$u'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$u'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_a_run_set_fun$ ?v3:A_run_set$ (((?v0 ≤ ?v1) ∧ ((fun_app$ag(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ less_eq$(fun_app$ag(?v2, ?v4), fun_app$ag(?v2, ?v5))))) ⇒ less_eq$(fun_app$ag(?v2, ?v0), ?v3))
tff(axiom378,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_a_run_set_fun$',A__questionmark_v3: 'A_run_set$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$ag'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'less_eq$'('fun_app$ag'(A__questionmark_v2,A__questionmark_v4),'fun_app$ag'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'less_eq$'('fun_app$ag'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_nat_fun$ ?v3:Nat$ (((?v0 ≤ ?v1) ∧ ((fun_app$t(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v2, ?v4)), fun_app$t(?v2, ?v5))))) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$t(?v2, ?v0)), ?v3))
tff(axiom379,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_nat_fun$',A__questionmark_v3: 'Nat$'] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$t'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v2,A__questionmark_v4)),'fun_app$t'(A__questionmark_v2,A__questionmark_v5)) ) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$t'(A__questionmark_v2,A__questionmark_v0)),A__questionmark_v3) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int_int_fun$ ?v3:Int (((?v0 ≤ ?v1) ∧ ((fun_app$ac(?v2, ?v1) = ?v3) ∧ ∀ ?v4:Int ?v5:Int ((?v4 ≤ ?v5) ⇒ (fun_app$ac(?v2, ?v4) ≤ fun_app$ac(?v2, ?v5))))) ⇒ (fun_app$ac(?v2, ?v0) ≤ ?v3))
tff(axiom380,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: 'Int_int_fun$',A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( 'fun_app$ac'(A__questionmark_v2,A__questionmark_v1) = A__questionmark_v3 )
        & ! [A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( $lesseq(A__questionmark_v4,A__questionmark_v5)
           => $lesseq('fun_app$ac'(A__questionmark_v2,A__questionmark_v4),'fun_app$ac'(A__questionmark_v2,A__questionmark_v5)) ) )
     => $lesseq('fun_app$ac'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v3) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ false) ∧ (fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0) ⇒ false)) ⇒ false)
tff(axiom381,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
         => $false )
        & ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ((((?v0 ≤ ?v1) ⇒ false) ∧ ((?v1 ≤ ?v0) ⇒ false)) ⇒ false)
tff(axiom382,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
         => $false )
        & ( $lesseq(A__questionmark_v1,A__questionmark_v0)
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (less_eq$(?v1, ?v0) = (?v1 = ?v0)))
tff(axiom383,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'less_eq$'(A__questionmark_v1,A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0) = (?v1 = ?v0)))
tff(axiom384,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ ((?v1 ≤ ?v0) = (?v1 = ?v0)))
tff(axiom385,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( $lesseq(A__questionmark_v1,A__questionmark_v0)
      <=> ( A__questionmark_v1 = A__questionmark_v0 ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((?v0 = fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), ?v3) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v2), ?v3))))
tff(axiom386,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) )
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v3) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v3)) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((?v0 = fun_app$q(fun_app$r(inf$, ?v1), ?v2)) ⇒ (fun_app$q(fun_app$r(inf$, ?v3), ?v0) = fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(fun_app$r(inf$, ?v3), ?v2))))
tff(axiom387,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) )
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v3),A__questionmark_v0) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v3),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$a(fun_app$b(fun_app$w(inf$a(uuh$(?v0)), uuh$(?v1)), ?v2), ?v3) = member$a(fun_app$c(fun_app$d(pair$, ?v2), ?v3), inf$j(?v0, ?v1)))
tff(axiom388,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$a'('fun_app$b'('fun_app$w'('inf$a'('uuh$'(A__questionmark_v0)),'uuh$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3),'inf$j'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$i(fun_app$j(fun_app$z(inf$d(uui$(?v0)), uui$(?v1)), ?v2), ?v3) = member$c(fun_app$k(fun_app$l(pair$b, ?v2), ?v3), inf$i(?v0, ?v1)))
tff(axiom389,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$i'('fun_app$j'('fun_app$z'('inf$d'('uui$'(A__questionmark_v0)),'uui$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3),'inf$i'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (fun_app$e(fun_app$f(fun_app$x(inf$b(uuj$(?v0)), uuj$(?v1)), ?v2), ?v3) = member$b(fun_app$g(fun_app$h(pair$a, ?v2), ?v3), inf$h(?v0, ?v1)))
tff(axiom390,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( 'fun_app$e'('fun_app$f'('fun_app$x'('inf$b'('uuj$'(A__questionmark_v0)),'uuj$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3),'inf$h'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ((uuh$(?v0) = uuh$(?v1)) = (?v0 = ?v1))
tff(axiom391,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( ( 'uuh$'(A__questionmark_v0) = 'uuh$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ((uui$(?v0) = uui$(?v1)) = (?v0 = ?v1))
tff(axiom392,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( ( 'uui$'(A__questionmark_v0) = 'uui$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ((uuj$(?v0) = uuj$(?v1)) = (?v0 = ?v1))
tff(axiom393,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( ( 'uuj$'(A__questionmark_v0) = 'uuj$'(A__questionmark_v1) )
    <=> ( A__questionmark_v0 = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ (∀ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (member$a(fun_app$c(fun_app$d(pair$, ?v2), ?v3), ?v0) ⇒ member$a(fun_app$c(fun_app$d(pair$, ?v2), ?v3), ?v1)) ⇒ less_eq$i(?v0, ?v1))
tff(axiom394,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$'] :
      ( ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
          ( 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3),A__questionmark_v0)
         => 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3),A__questionmark_v1) )
     => 'less_eq$i'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ (∀ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (member$c(fun_app$k(fun_app$l(pair$b, ?v2), ?v3), ?v0) ⇒ member$c(fun_app$k(fun_app$l(pair$b, ?v2), ?v3), ?v1)) ⇒ less_eq$h(?v0, ?v1))
tff(axiom395,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$'] :
      ( ! [A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
          ( 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3),A__questionmark_v0)
         => 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3),A__questionmark_v1) )
     => 'less_eq$h'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ (∀ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (member$b(fun_app$g(fun_app$h(pair$a, ?v2), ?v3), ?v0) ⇒ member$b(fun_app$g(fun_app$h(pair$a, ?v2), ?v3), ?v1)) ⇒ less_eq$g(?v0, ?v1))
tff(axiom396,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$'] :
      ( ! [A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
          ( 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3),A__questionmark_v0)
         => 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3),A__questionmark_v1) )
     => 'less_eq$g'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$c(uud$(?v0), uud$(?v1)) = less_eq$(?v0, ?v1))
tff(axiom397,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$c'('uud$'(A__questionmark_v0),'uud$'(A__questionmark_v1))
    <=> 'less_eq$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_TESL_atomic$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic_list$ ((cons$(?v0, ?v1) = cons$(?v2, ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom398,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( ( 'cons$'(A__questionmark_v0,A__questionmark_v1) = 'cons$'(A__questionmark_v2,A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_constr$ ?v1:A_constr_list$ ?v2:A_constr$ ?v3:A_constr_list$ ((cons$a(?v0, ?v1) = cons$a(?v2, ?v3)) = ((?v0 = ?v2) ∧ (?v1 = ?v3)))
tff(axiom399,axiom,
    ! [A__questionmark_v0: 'A_constr$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'A_constr$',A__questionmark_v3: 'A_constr_list$'] :
      ( ( 'cons$a'(A__questionmark_v0,A__questionmark_v1) = 'cons$a'(A__questionmark_v2,A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( A__questionmark_v1 = A__questionmark_v3 ) ) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_run_set$ (((heronConf_interpretation$(?v0) = ?v1) ∧ (fun_app$v(accp$(heronConf_interpretation_rel$), ?v0) ∧ ∀ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))) ∧ ((?v1 = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, symbolic_run_interpretation$(?v2)), fun_app$s(tESL_interpretation_stepwise$(?v4), ?v3))), fun_app$s(tESL_interpretation_stepwise$(?v5), fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1))))) ∧ fun_app$v(accp$(heronConf_interpretation_rel$), fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, ?v4), ?v5)))))) ⇒ false))) ⇒ false)
tff(axiom400,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_run_set$'] :
      ( ( ( 'heronConf_interpretation$'(A__questionmark_v0) = A__questionmark_v1 )
        & 'fun_app$v'('accp$'('heronConf_interpretation_rel$'),A__questionmark_v0)
        & ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5))) )
              & ( A__questionmark_v1 = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','symbolic_run_interpretation$'(A__questionmark_v2)),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v4),A__questionmark_v3))),'fun_app$s'('tESL_interpretation_stepwise$'(A__questionmark_v5),'fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1)))) )
              & 'fun_app$v'('accp$'('heronConf_interpretation_rel$'),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),A__questionmark_v5)))) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(strictlyPrecedes$(?v2, ?v3), ?v4)), ?v5)))), fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v3, ?v1), tickCountLess$(?v2, ?v1), case_prod$(less_eq$f)), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(strictlyPrecedes$(?v2, ?v3), ?v5)))))
tff(axiom401,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v3,A__questionmark_v1),'tickCountLess$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(strictlyPrecedes$(?v2, ?v3), ?v4)), ?v5)))) = heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v3, ?v1), tickCountLess$(?v2, ?v1), case_prod$(less_eq$f)), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(strictlyPrecedes$(?v2, ?v3), ?v5))))))
tff(axiom402,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))) = 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v3,A__questionmark_v1),'tickCountLess$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ) ).

%% ∀ ?v0:Nat_nat_prod$ ?v1:Nat_nat_bool_fun_fun$ ?v2:Nat_nat_bool_fun_fun$ ?v3:Nat_nat_prod$ ((∀ ?v4:Nat$ ?v5:Nat$ ((pair$c(?v4, ?v5) = ?v0) ⇒ (fun_app$m(fun_app$n(?v1, ?v4), ?v5) = fun_app$m(fun_app$n(?v2, ?v4), ?v5))) ∧ (?v3 = ?v0)) ⇒ (fun_app$o(case_prod$(?v1), ?v3) = fun_app$o(case_prod$(?v2), ?v0)))
tff(axiom403,axiom,
    ! [A__questionmark_v0: 'Nat_nat_prod$',A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_bool_fun_fun$',A__questionmark_v3: 'Nat_nat_prod$'] :
      ( ( ! [A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( 'pair$c'(A__questionmark_v4,A__questionmark_v5) = A__questionmark_v0 )
           => ( 'fun_app$m'('fun_app$n'(A__questionmark_v1,A__questionmark_v4),A__questionmark_v5)
            <=> 'fun_app$m'('fun_app$n'(A__questionmark_v2,A__questionmark_v4),A__questionmark_v5) ) )
        & ( A__questionmark_v3 = A__questionmark_v0 ) )
     => ( 'fun_app$o'('case_prod$'(A__questionmark_v1),A__questionmark_v3)
      <=> 'fun_app$o'('case_prod$'(A__questionmark_v2),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Clock$ ?v3:Nat$ ((tickCountLess$(?v0, ?v1) = tickCountLess$(?v2, ?v3)) = ((?v0 = ?v2) ∧ (fun_app$u(of_nat$, ?v1) = fun_app$u(of_nat$, ?v3))))
tff(axiom404,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Nat$'] :
      ( ( 'tickCountLess$'(A__questionmark_v0,A__questionmark_v1) = 'tickCountLess$'(A__questionmark_v2,A__questionmark_v3) )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & ( 'fun_app$u'('of_nat$',A__questionmark_v1) = 'fun_app$u'('of_nat$',A__questionmark_v3) ) ) ) ).

%% ∀ ?v0:Clock$ ?v1:Clock$ ?v2:Clock$ ?v3:Clock$ ¬(weaklyPrecedes$(?v0, ?v1) = strictlyPrecedes$(?v2, ?v3))
tff(axiom405,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Clock$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$'] : ( 'weaklyPrecedes$'(A__questionmark_v0,A__questionmark_v1) != 'strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v3) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Clock$ ?v3:Nat$ ¬(tickCountLess$(?v0, ?v1) = tickCountLeq$(?v2, ?v3))
tff(axiom406,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Nat$'] : ( 'tickCountLess$'(A__questionmark_v0,A__questionmark_v1) != 'tickCountLeq$'(A__questionmark_v2,A__questionmark_v3) ) ).

%% ∀ ?v0:Cnt_expr$ ((∀ ?v1:Clock$ ?v2:Nat$ ((?v0 = tickCountLess$(?v1, ?v2)) ⇒ false) ∧ ∀ ?v1:Clock$ ?v2:Nat$ ((?v0 = tickCountLeq$(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom407,axiom,
    ! [A__questionmark_v0: 'Cnt_expr$'] :
      ( ( ! [A__questionmark_v1: 'Clock$',A__questionmark_v2: 'Nat$'] :
            ( ( A__questionmark_v0 = 'tickCountLess$'(A__questionmark_v1,A__questionmark_v2) )
           => $false )
        & ! [A__questionmark_v1: 'Clock$',A__questionmark_v2: 'Nat$'] :
            ( ( A__questionmark_v0 = 'tickCountLeq$'(A__questionmark_v1,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic$ ?v1:A_TESL_atomic_list$ ¬(cons$(?v0, ?v1) = ?v1)
tff(axiom408,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic$',A__questionmark_v1: 'A_TESL_atomic_list$'] : ( 'cons$'(A__questionmark_v0,A__questionmark_v1) != A__questionmark_v1 ) ).

%% ∀ ?v0:A_constr$ ?v1:A_constr_list$ ¬(cons$a(?v0, ?v1) = ?v1)
tff(axiom409,axiom,
    ! [A__questionmark_v0: 'A_constr$',A__questionmark_v1: 'A_constr_list$'] : ( 'cons$a'(A__questionmark_v0,A__questionmark_v1) != A__questionmark_v1 ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (case_prod$d(pair$, ?v0) = ?v0)
tff(axiom410,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] : ( 'case_prod$d'('pair$',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (case_prod$e(pair$b, ?v0) = ?v0)
tff(axiom411,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] : ( 'case_prod$e'('pair$b',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (case_prod$f(pair$a, ?v0) = ?v0)
tff(axiom412,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] : ( 'case_prod$f'('pair$a',A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Clock$ ?v3:A_constr_list$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v0, ?v1), tickCountLess$(?v2, ?v1), case_prod$(less_eq$f)), ?v3)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(strictlyPrecedes$(?v2, ?v0), ?v5)))), bot$), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v3), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(strictlyPrecedes$(?v2, ?v0), ?v4)), ?v5))))))
tff(axiom413,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'A_constr_list$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v0,A__questionmark_v1),'tickCountLess$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v3)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v5)))),'bot$'),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v3),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('strictlyPrecedes$'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v4)),A__questionmark_v5)))))) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Clock$ ?v3:A_constr_list$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, cons$a(tickCntArith$(tickCountLeq$(?v0, ?v1), tickCountLeq$(?v2, ?v1), case_prod$(less_eq$f)), ?v3)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(weaklyPrecedes$(?v2, ?v0), ?v5)))), bot$), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v3), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(weaklyPrecedes$(?v2, ?v0), ?v4)), ?v5))))))
tff(axiom414,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'A_constr_list$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('tickCntArith$'('tickCountLeq$'(A__questionmark_v0,A__questionmark_v1),'tickCountLeq$'(A__questionmark_v2,A__questionmark_v1),'case_prod$'('less_eq$f')),A__questionmark_v3)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v5)))),'bot$'),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v3),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v0),A__questionmark_v4)),A__questionmark_v5)))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:A_tag_const$ ?v4:Clock$ ?v5:A_TESL_atomic_list$ ?v6:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(sporadicOn$(?v2, ?v3, ?v4), ?v5)), ?v6)))), fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v5), cons$(sporadicOn$(?v2, ?v3, ?v4), ?v6)))))
tff(axiom415,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'A_tag_const$',A__questionmark_v4: 'Clock$',A__questionmark_v5: 'A_TESL_atomic_list$',A__questionmark_v6: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('sporadicOn$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4),A__questionmark_v5)),A__questionmark_v6)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v5),'cons$'('sporadicOn$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4),A__questionmark_v6))))) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, bot$a), ?v0) = bot$a)
tff(axiom416,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','bot$a'),A__questionmark_v0) = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), bot$a) = bot$a)
tff(axiom417,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'bot$a') = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, bot$a), ?v0) = bot$a)
tff(axiom418,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','bot$a'),A__questionmark_v0) = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), bot$a) = bot$a)
tff(axiom419,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'bot$a') = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ (less_eq$(?v0, bot$a) = (?v0 = bot$a))
tff(axiom420,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'bot$a')
    <=> ( A__questionmark_v0 = 'bot$a' ) ) ).

%% ∀ ?v0:A_run_set$ less_eq$(bot$a, ?v0)
tff(axiom421,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : 'less_eq$'('bot$a',A__questionmark_v0) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(fun_app$q(insert$a(?v0), ?v1), ?v2) = (member$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)))
tff(axiom422,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'('fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'member$'(A__questionmark_v0,A__questionmark_v2)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (¬member$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v2)), ?v1) = fun_app$q(fun_app$r(inf$, ?v2), ?v1)))
tff(axiom423,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ~ 'member$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (member$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v2)), ?v1) = fun_app$q(insert$a(?v0), fun_app$q(fun_app$r(inf$, ?v2), ?v1))))
tff(axiom424,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'member$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) = 'fun_app$q'('insert$a'(A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v1)) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v1)), fun_app$q(insert$a(?v0), ?v2)) = fun_app$q(insert$a(?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom425,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2)) = 'fun_app$q'('insert$a'(A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (¬member$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(insert$a(?v0), ?v2)) = fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom426,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ~ 'member$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (member$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(inf$, ?v1), fun_app$q(insert$a(?v0), ?v2)) = fun_app$q(insert$a(?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2))))
tff(axiom427,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'member$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),'fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2)) = 'fun_app$q'('insert$a'(A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run$ ?v2:A_run_set$ ((fun_app$q(insert$a(?v0), bot$a) = fun_app$q(insert$a(?v1), ?v2)) = ((?v1 = ?v0) ∧ less_eq$(?v2, fun_app$q(insert$a(?v0), bot$a))))
tff(axiom428,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'fun_app$q'('insert$a'(A__questionmark_v0),'bot$a') = 'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v2) )
    <=> ( ( A__questionmark_v1 = A__questionmark_v0 )
        & 'less_eq$'(A__questionmark_v2,'fun_app$q'('insert$a'(A__questionmark_v0),'bot$a')) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run$ ((fun_app$q(insert$a(?v0), ?v1) = fun_app$q(insert$a(?v2), bot$a)) = ((?v0 = ?v2) ∧ less_eq$(?v1, fun_app$q(insert$a(?v2), bot$a))))
tff(axiom429,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( ( 'fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1) = 'fun_app$q'('insert$a'(A__questionmark_v2),'bot$a') )
    <=> ( ( A__questionmark_v0 = A__questionmark_v2 )
        & 'less_eq$'(A__questionmark_v1,'fun_app$q'('insert$a'(A__questionmark_v2),'bot$a')) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ ((fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v1)), ?v2) = bot$a) = (¬member$(?v0, ?v2) ∧ (fun_app$q(fun_app$r(inf$, ?v1), ?v2) = bot$a)))
tff(axiom430,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'bot$a' )
    <=> ( ~ 'member$'(A__questionmark_v0,A__questionmark_v2)
        & ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) = 'bot$a' ) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ ((bot$a = fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v1)), ?v2)) = (¬member$(?v0, ?v2) ∧ (bot$a = fun_app$q(fun_app$r(inf$, ?v1), ?v2))))
tff(axiom431,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'bot$a' = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) )
    <=> ( ~ 'member$'(A__questionmark_v0,A__questionmark_v2)
        & ( 'bot$a' = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ ?v2:A_run_set$ ((fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(insert$a(?v1), ?v2)) = bot$a) = (¬member$(?v1, ?v0) ∧ (fun_app$q(fun_app$r(inf$, ?v0), ?v2) = bot$a)))
tff(axiom432,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v2)) = 'bot$a' )
    <=> ( ~ 'member$'(A__questionmark_v1,A__questionmark_v0)
        & ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2) = 'bot$a' ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ ?v2:A_run_set$ ((bot$a = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(insert$a(?v1), ?v2))) = (¬member$(?v1, ?v0) ∧ (bot$a = fun_app$q(fun_app$r(inf$, ?v0), ?v2))))
tff(axiom433,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'bot$a' = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v2)) )
    <=> ( ~ 'member$'(A__questionmark_v1,A__questionmark_v0)
        & ( 'bot$a' = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ (less_eq$(?v0, fun_app$q(insert$a(?v1), bot$a)) ⇒ ((?v0 = bot$a) ∨ (?v0 = fun_app$q(insert$a(?v1), bot$a))))
tff(axiom434,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$'] :
      ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('insert$a'(A__questionmark_v1),'bot$a'))
     => ( ( A__questionmark_v0 = 'bot$a' )
        | ( A__questionmark_v0 = 'fun_app$q'('insert$a'(A__questionmark_v1),'bot$a') ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ (less_eq$(?v0, fun_app$q(insert$a(?v1), bot$a)) = ((?v0 = bot$a) ∨ (?v0 = fun_app$q(insert$a(?v1), bot$a))))
tff(axiom435,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$'] :
      ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('insert$a'(A__questionmark_v1),'bot$a'))
    <=> ( ( A__questionmark_v0 = 'bot$a' )
        | ( A__questionmark_v0 = 'fun_app$q'('insert$a'(A__questionmark_v1),'bot$a') ) ) ) ).

%% ∀ ?v0:A_run_set$ (less_eq$(?v0, bot$a) ⇒ (?v0 = bot$a))
tff(axiom436,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'bot$a')
     => ( A__questionmark_v0 = 'bot$a' ) ) ).

%% ∀ ?v0:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), bot$b) ⇒ (?v0 = bot$b))
tff(axiom437,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'bot$b')
     => ( A__questionmark_v0 = 'bot$b' ) ) ).

%% ∀ ?v0:A_run_set$ (less_eq$(?v0, bot$a) = (?v0 = bot$a))
tff(axiom438,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,'bot$a')
    <=> ( A__questionmark_v0 = 'bot$a' ) ) ).

%% ∀ ?v0:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), bot$b) = (?v0 = bot$b))
tff(axiom439,axiom,
    ! [A__questionmark_v0: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'bot$b')
    <=> ( A__questionmark_v0 = 'bot$b' ) ) ).

%% ∀ ?v0:A_run_set$ less_eq$(bot$a, ?v0)
tff(axiom440,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : 'less_eq$'('bot$a',A__questionmark_v0) ).

%% ∀ ?v0:Nat$ fun_app$m(fun_app$n(less_eq$f, bot$b), ?v0)
tff(axiom441,axiom,
    ! [A__questionmark_v0: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','bot$b'),A__questionmark_v0) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ (less_eq$(?v0, ?v1) ⇒ less_eq$(?v0, fun_app$q(insert$a(?v2), ?v1)))
tff(axiom442,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('insert$a'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ less_eq$(?v0, fun_app$q(insert$a(?v1), ?v0))
tff(axiom443,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (¬member$(?v0, ?v1) ⇒ (less_eq$(?v1, fun_app$q(insert$a(?v0), ?v2)) = less_eq$(?v1, ?v2)))
tff(axiom444,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ~ 'member$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'less_eq$'(A__questionmark_v1,'fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v2))
      <=> 'less_eq$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run$ (less_eq$(?v0, ?v1) ⇒ less_eq$(fun_app$q(insert$a(?v2), ?v0), fun_app$q(insert$a(?v2), ?v1)))
tff(axiom445,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'('fun_app$q'('insert$a'(A__questionmark_v2),A__questionmark_v0),'fun_app$q'('insert$a'(A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(insert$a(?v1), ?v2)) = (if member$(?v1, ?v0) fun_app$q(insert$a(?v1), fun_app$q(fun_app$r(inf$, ?v0), ?v2)) else fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom446,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'member$'(A__questionmark_v1,A__questionmark_v0)
       => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('insert$a'(A__questionmark_v1),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) )
      & ( ~ 'member$'(A__questionmark_v1,A__questionmark_v0)
       => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('insert$a'(A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:A_run$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(insert$a(?v0), ?v1)), ?v2) = (if member$(?v0, ?v2) fun_app$q(insert$a(?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) else fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom447,axiom,
    ! [A__questionmark_v0: 'A_run$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'member$'(A__questionmark_v0,A__questionmark_v2)
       => ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('insert$a'(A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) )
      & ( ~ 'member$'(A__questionmark_v0,A__questionmark_v2)
       => ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('insert$a'(A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2) ) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((fun_app$q(fun_app$r(inf$, ?v0), ?v1) = bot$a) = ∀ ?v2:A_run$ (member$(?v2, ?v0) ⇒ ∀ ?v3:A_run$ (member$(?v3, ?v1) ⇒ ¬(?v2 = ?v3))))
tff(axiom448,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'bot$a' )
    <=> ! [A__questionmark_v2: 'A_run$'] :
          ( 'member$'(A__questionmark_v2,A__questionmark_v0)
         => ! [A__questionmark_v3: 'A_run$'] :
              ( 'member$'(A__questionmark_v3,A__questionmark_v1)
             => ( A__questionmark_v2 != A__questionmark_v3 ) ) ) ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), bot$a) = bot$a)
tff(axiom449,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'bot$a') = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ (fun_app$q(fun_app$r(inf$, bot$a), ?v0) = bot$a)
tff(axiom450,axiom,
    ! [A__questionmark_v0: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','bot$a'),A__questionmark_v0) = 'bot$a' ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((fun_app$q(fun_app$r(inf$, ?v0), ?v1) = bot$a) = ∀ ?v2:A_run$ (member$(?v2, ?v0) ⇒ ¬member$(?v2, ?v1)))
tff(axiom451,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'bot$a' )
    <=> ! [A__questionmark_v2: 'A_run$'] :
          ( 'member$'(A__questionmark_v2,A__questionmark_v0)
         => ~ 'member$'(A__questionmark_v2,A__questionmark_v1) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (∀ ?v2:A_run$ ((member$(?v2, ?v0) ∧ member$(?v2, ?v1)) ⇒ false) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), ?v1) = bot$a))
tff(axiom452,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ! [A__questionmark_v2: 'A_run$'] :
          ( ( 'member$'(A__questionmark_v2,A__questionmark_v0)
            & 'member$'(A__questionmark_v2,A__questionmark_v1) )
         => $false )
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1) = 'bot$a' ) ) ).

%% ∀ ?v0:Clock$ ?v1:A_tag_const$ ?v2:Clock$ ?v3:Clock$ ?v4:Clock$ ¬(sporadicOn$(?v0, ?v1, ?v2) = weaklyPrecedes$(?v3, ?v4))
tff(axiom453,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'A_tag_const$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'Clock$'] : ( 'sporadicOn$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) != 'weaklyPrecedes$'(A__questionmark_v3,A__questionmark_v4) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, fun_app$t(nat$, (fun_app$u(of_nat$, ?v1) + 1))), fun_app$g(fun_app$h(pair$a, ?v2), nil$))), bot$), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, nil$), ?v2))))))
tff(axiom454,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b','fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),'nil$'))),'bot$'),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v2)))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ ?v3:Clock$ ?v4:A_tag_const$ ?v5:Clock$ ?v6:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), cons$(sporadicOn$(?v3, ?v4, ?v5), ?v6)))), insert$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v3, ?v1), cons$a(timestamp$(?v5, ?v1, ?v4), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v2), ?v6))), bot$)), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(sporadicOn$(?v3, ?v4, ?v5), ?v2)), ?v6))))))
tff(axiom455,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_tag_const$',A__questionmark_v5: 'Clock$',A__questionmark_v6: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),'cons$'('sporadicOn$'(A__questionmark_v3,A__questionmark_v4,A__questionmark_v5),A__questionmark_v6)))),'insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v3,A__questionmark_v1),'cons$a'('timestamp$'(A__questionmark_v5,A__questionmark_v1,A__questionmark_v4),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v6))),'bot$')),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('sporadicOn$'(A__questionmark_v3,A__questionmark_v4,A__questionmark_v5),A__questionmark_v2)),A__questionmark_v6)))))) ).

%% ∀ ?v0:A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$ ((∀ ?v1:A_TESL_atomic_a_TESL_atomic_bool_fun_fun$ ((?v0 = pair$d(?v1, nil$)) ⇒ false) ∧ (∀ ?v1:A_TESL_atomic_a_TESL_atomic_bool_fun_fun$ ?v2:A_TESL_atomic$ ((?v0 = pair$d(?v1, cons$(?v2, nil$))) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic_a_TESL_atomic_bool_fun_fun$ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ ((?v0 = pair$d(?v1, cons$(?v2, cons$(?v3, ?v4)))) ⇒ false))) ⇒ false)
tff(axiom456,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$'] :
            ( ( A__questionmark_v0 = 'pair$d'(A__questionmark_v1,'nil$') )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic$'] :
            ( ( A__questionmark_v0 = 'pair$d'(A__questionmark_v1,'cons$'(A__questionmark_v2,'nil$')) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'pair$d'(A__questionmark_v1,'cons$'(A__questionmark_v2,'cons$'(A__questionmark_v3,A__questionmark_v4))) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_a_constr_bool_fun_fun_a_constr_list_prod$ ((∀ ?v1:A_constr_a_constr_bool_fun_fun$ ((?v0 = pair$e(?v1, nil$a)) ⇒ false) ∧ (∀ ?v1:A_constr_a_constr_bool_fun_fun$ ?v2:A_constr$ ((?v0 = pair$e(?v1, cons$a(?v2, nil$a))) ⇒ false) ∧ ∀ ?v1:A_constr_a_constr_bool_fun_fun$ ?v2:A_constr$ ?v3:A_constr$ ?v4:A_constr_list$ ((?v0 = pair$e(?v1, cons$a(?v2, cons$a(?v3, ?v4)))) ⇒ false))) ⇒ false)
tff(axiom457,axiom,
    ! [A__questionmark_v0: 'A_constr_a_constr_bool_fun_fun_a_constr_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_constr_a_constr_bool_fun_fun$'] :
            ( ( A__questionmark_v0 = 'pair$e'(A__questionmark_v1,'nil$a') )
           => $false )
        & ! [A__questionmark_v1: 'A_constr_a_constr_bool_fun_fun$',A__questionmark_v2: 'A_constr$'] :
            ( ( A__questionmark_v0 = 'pair$e'(A__questionmark_v1,'cons$a'(A__questionmark_v2,'nil$a')) )
           => $false )
        & ! [A__questionmark_v1: 'A_constr_a_constr_bool_fun_fun$',A__questionmark_v2: 'A_constr$',A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$e'(A__questionmark_v1,'cons$a'(A__questionmark_v2,'cons$a'(A__questionmark_v3,A__questionmark_v4))) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$ ((∀ ?v1:A_TESL_atomic_a_TESL_atomic_bool_fun_fun$ ((?v0 = pair$d(?v1, nil$)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic_a_TESL_atomic_bool_fun_fun$ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic_list$ ((?v0 = pair$d(?v1, cons$(?v2, ?v3))) ⇒ false)) ⇒ false)
tff(axiom458,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun_a_TESL_atomic_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$'] :
            ( ( A__questionmark_v0 = 'pair$d'(A__questionmark_v1,'nil$') )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_bool_fun_fun$',A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'pair$d'(A__questionmark_v1,'cons$'(A__questionmark_v2,A__questionmark_v3)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_a_constr_bool_fun_fun_a_constr_list_prod$ ((∀ ?v1:A_constr_a_constr_bool_fun_fun$ ((?v0 = pair$e(?v1, nil$a)) ⇒ false) ∧ ∀ ?v1:A_constr_a_constr_bool_fun_fun$ ?v2:A_constr$ ?v3:A_constr_list$ ((?v0 = pair$e(?v1, cons$a(?v2, ?v3))) ⇒ false)) ⇒ false)
tff(axiom459,axiom,
    ! [A__questionmark_v0: 'A_constr_a_constr_bool_fun_fun_a_constr_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_constr_a_constr_bool_fun_fun$'] :
            ( ( A__questionmark_v0 = 'pair$e'(A__questionmark_v1,'nil$a') )
           => $false )
        & ! [A__questionmark_v1: 'A_constr_a_constr_bool_fun_fun$',A__questionmark_v2: 'A_constr$',A__questionmark_v3: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$e'(A__questionmark_v1,'cons$a'(A__questionmark_v2,A__questionmark_v3)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_nat_prod$ ((∀ ?v1:Nat$ ((?v0 = pair$f(nil$, ?v1)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ?v3:Nat$ ((?v0 = pair$f(cons$(?v1, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom460,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_nat_prod$'] :
      ( ( ! [A__questionmark_v1: 'Nat$'] :
            ( ( A__questionmark_v0 = 'pair$f'('nil$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'Nat$'] :
            ( ( A__questionmark_v0 = 'pair$f'('cons$'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_list$ ((((?v0 = nil$b) ⇒ false) ∧ (∀ ?v1:A_TESL_atomic_list_list$ ((?v0 = cons$b(nil$, ?v1)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list_list$ ((?v0 = cons$b(cons$(?v1, ?v2), ?v3)) ⇒ false))) ⇒ false)
tff(axiom461,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$b' )
         => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_list_list$'] :
            ( ( A__questionmark_v0 = 'cons$b'('nil$',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list_list$'] :
            ( ( A__questionmark_v0 = 'cons$b'('cons$'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list_list$ ((((?v0 = nil$c) ⇒ false) ∧ (∀ ?v1:A_constr_list_list$ ((?v0 = cons$c(nil$a, ?v1)) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr_list$ ?v3:A_constr_list_list$ ((?v0 = cons$c(cons$a(?v1, ?v2), ?v3)) ⇒ false))) ⇒ false)
tff(axiom462,axiom,
    ! [A__questionmark_v0: 'A_constr_list_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$c' )
         => $false )
        & ! [A__questionmark_v1: 'A_constr_list_list$'] :
            ( ( A__questionmark_v0 = 'cons$c'('nil$a',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'A_constr_list_list$'] :
            ( ( A__questionmark_v0 = 'cons$c'('cons$a'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic_list_bool_fun$ ((¬(?v0 = nil$) ∧ (∀ ?v2:A_TESL_atomic$ fun_app$e(?v1, cons$(?v2, nil$)) ∧ ∀ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic_list$ ((¬(?v3 = nil$) ∧ fun_app$e(?v1, ?v3)) ⇒ fun_app$e(?v1, cons$(?v2, ?v3))))) ⇒ fun_app$e(?v1, ?v0))
tff(axiom463,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic_list_bool_fun$'] :
      ( ( ( A__questionmark_v0 != 'nil$' )
        & ! [A__questionmark_v2: 'A_TESL_atomic$'] : 'fun_app$e'(A__questionmark_v1,'cons$'(A__questionmark_v2,'nil$'))
        & ! [A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
            ( ( ( A__questionmark_v3 != 'nil$' )
              & 'fun_app$e'(A__questionmark_v1,A__questionmark_v3) )
           => 'fun_app$e'(A__questionmark_v1,'cons$'(A__questionmark_v2,A__questionmark_v3)) ) )
     => 'fun_app$e'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:A_constr_list_bool_fun$ ((¬(?v0 = nil$a) ∧ (∀ ?v2:A_constr$ fun_app$aj(?v1, cons$a(?v2, nil$a)) ∧ ∀ ?v2:A_constr$ ?v3:A_constr_list$ ((¬(?v3 = nil$a) ∧ fun_app$aj(?v1, ?v3)) ⇒ fun_app$aj(?v1, cons$a(?v2, ?v3))))) ⇒ fun_app$aj(?v1, ?v0))
tff(axiom464,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'A_constr_list_bool_fun$'] :
      ( ( ( A__questionmark_v0 != 'nil$a' )
        & ! [A__questionmark_v2: 'A_constr$'] : 'fun_app$aj'(A__questionmark_v1,'cons$a'(A__questionmark_v2,'nil$a'))
        & ! [A__questionmark_v2: 'A_constr$',A__questionmark_v3: 'A_constr_list$'] :
            ( ( ( A__questionmark_v3 != 'nil$a' )
              & 'fun_app$aj'(A__questionmark_v1,A__questionmark_v3) )
           => 'fun_app$aj'(A__questionmark_v1,'cons$a'(A__questionmark_v2,A__questionmark_v3)) ) )
     => 'fun_app$aj'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_TESL_atomic_list$ ?v2:A_TESL_atomic_list$ ((fun_app$e(fun_app$f(?v0, nil$), nil$) ∧ (∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ fun_app$e(fun_app$f(?v0, cons$(?v3, ?v4)), nil$) ∧ (∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ fun_app$e(fun_app$f(?v0, nil$), cons$(?v3, ?v4)) ∧ ∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic$ ?v6:A_TESL_atomic_list$ (fun_app$e(fun_app$f(?v0, ?v4), ?v6) ⇒ fun_app$e(fun_app$f(?v0, cons$(?v3, ?v4)), cons$(?v5, ?v6)))))) ⇒ fun_app$e(fun_app$f(?v0, ?v1), ?v2))
tff(axiom465,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( ( 'fun_app$e'('fun_app$f'(A__questionmark_v0,'nil$'),'nil$')
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] : 'fun_app$e'('fun_app$f'(A__questionmark_v0,'cons$'(A__questionmark_v3,A__questionmark_v4)),'nil$')
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] : 'fun_app$e'('fun_app$f'(A__questionmark_v0,'nil$'),'cons$'(A__questionmark_v3,A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic$',A__questionmark_v6: 'A_TESL_atomic_list$'] :
            ( 'fun_app$e'('fun_app$f'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v6)
           => 'fun_app$e'('fun_app$f'(A__questionmark_v0,'cons$'(A__questionmark_v3,A__questionmark_v4)),'cons$'(A__questionmark_v5,A__questionmark_v6)) ) )
     => 'fun_app$e'('fun_app$f'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_constr_list_bool_fun_fun$ ?v1:A_TESL_atomic_list$ ?v2:A_constr_list$ ((fun_app$aj(fun_app$ak(?v0, nil$), nil$a) ∧ (∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ fun_app$aj(fun_app$ak(?v0, cons$(?v3, ?v4)), nil$a) ∧ (∀ ?v3:A_constr$ ?v4:A_constr_list$ fun_app$aj(fun_app$ak(?v0, nil$), cons$a(?v3, ?v4)) ∧ ∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ ?v5:A_constr$ ?v6:A_constr_list$ (fun_app$aj(fun_app$ak(?v0, ?v4), ?v6) ⇒ fun_app$aj(fun_app$ak(?v0, cons$(?v3, ?v4)), cons$a(?v5, ?v6)))))) ⇒ fun_app$aj(fun_app$ak(?v0, ?v1), ?v2))
tff(axiom466,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_constr_list_bool_fun_fun$',A__questionmark_v1: 'A_TESL_atomic_list$',A__questionmark_v2: 'A_constr_list$'] :
      ( ( 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,'nil$'),'nil$a')
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] : 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,'cons$'(A__questionmark_v3,A__questionmark_v4)),'nil$a')
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] : 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,'nil$'),'cons$a'(A__questionmark_v3,A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_constr$',A__questionmark_v6: 'A_constr_list$'] :
            ( 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v6)
           => 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,'cons$'(A__questionmark_v3,A__questionmark_v4)),'cons$a'(A__questionmark_v5,A__questionmark_v6)) ) )
     => 'fun_app$aj'('fun_app$ak'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list_a_TESL_atomic_list_bool_fun_fun$ ?v1:A_constr_list$ ?v2:A_TESL_atomic_list$ ((fun_app$e(fun_app$al(?v0, nil$a), nil$) ∧ (∀ ?v3:A_constr$ ?v4:A_constr_list$ fun_app$e(fun_app$al(?v0, cons$a(?v3, ?v4)), nil$) ∧ (∀ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ fun_app$e(fun_app$al(?v0, nil$a), cons$(?v3, ?v4)) ∧ ∀ ?v3:A_constr$ ?v4:A_constr_list$ ?v5:A_TESL_atomic$ ?v6:A_TESL_atomic_list$ (fun_app$e(fun_app$al(?v0, ?v4), ?v6) ⇒ fun_app$e(fun_app$al(?v0, cons$a(?v3, ?v4)), cons$(?v5, ?v6)))))) ⇒ fun_app$e(fun_app$al(?v0, ?v1), ?v2))
tff(axiom467,axiom,
    ! [A__questionmark_v0: 'A_constr_list_a_TESL_atomic_list_bool_fun_fun$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( ( 'fun_app$e'('fun_app$al'(A__questionmark_v0,'nil$a'),'nil$')
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] : 'fun_app$e'('fun_app$al'(A__questionmark_v0,'cons$a'(A__questionmark_v3,A__questionmark_v4)),'nil$')
        & ! [A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] : 'fun_app$e'('fun_app$al'(A__questionmark_v0,'nil$a'),'cons$'(A__questionmark_v3,A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$',A__questionmark_v5: 'A_TESL_atomic$',A__questionmark_v6: 'A_TESL_atomic_list$'] :
            ( 'fun_app$e'('fun_app$al'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v6)
           => 'fun_app$e'('fun_app$al'(A__questionmark_v0,'cons$a'(A__questionmark_v3,A__questionmark_v4)),'cons$'(A__questionmark_v5,A__questionmark_v6)) ) )
     => 'fun_app$e'('fun_app$al'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_constr_list_a_constr_list_bool_fun_fun$ ?v1:A_constr_list$ ?v2:A_constr_list$ ((fun_app$aj(fun_app$am(?v0, nil$a), nil$a) ∧ (∀ ?v3:A_constr$ ?v4:A_constr_list$ fun_app$aj(fun_app$am(?v0, cons$a(?v3, ?v4)), nil$a) ∧ (∀ ?v3:A_constr$ ?v4:A_constr_list$ fun_app$aj(fun_app$am(?v0, nil$a), cons$a(?v3, ?v4)) ∧ ∀ ?v3:A_constr$ ?v4:A_constr_list$ ?v5:A_constr$ ?v6:A_constr_list$ (fun_app$aj(fun_app$am(?v0, ?v4), ?v6) ⇒ fun_app$aj(fun_app$am(?v0, cons$a(?v3, ?v4)), cons$a(?v5, ?v6)))))) ⇒ fun_app$aj(fun_app$am(?v0, ?v1), ?v2))
tff(axiom468,axiom,
    ! [A__questionmark_v0: 'A_constr_list_a_constr_list_bool_fun_fun$',A__questionmark_v1: 'A_constr_list$',A__questionmark_v2: 'A_constr_list$'] :
      ( ( 'fun_app$aj'('fun_app$am'(A__questionmark_v0,'nil$a'),'nil$a')
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] : 'fun_app$aj'('fun_app$am'(A__questionmark_v0,'cons$a'(A__questionmark_v3,A__questionmark_v4)),'nil$a')
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] : 'fun_app$aj'('fun_app$am'(A__questionmark_v0,'nil$a'),'cons$a'(A__questionmark_v3,A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$',A__questionmark_v5: 'A_constr$',A__questionmark_v6: 'A_constr_list$'] :
            ( 'fun_app$aj'('fun_app$am'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v6)
           => 'fun_app$aj'('fun_app$am'(A__questionmark_v0,'cons$a'(A__questionmark_v3,A__questionmark_v4)),'cons$a'(A__questionmark_v5,A__questionmark_v6)) ) )
     => 'fun_app$aj'('fun_app$am'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ ?v0:A_TESL_atomic_list$ (¬(?v0 = nil$) = ∃ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ (?v0 = cons$(?v1, ?v2)))
tff(axiom469,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$'] :
      ( ( A__questionmark_v0 != 'nil$' )
    <=> ? [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$'] : ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_constr_list$ (¬(?v0 = nil$a) = ∃ ?v1:A_constr$ ?v2:A_constr_list$ (?v0 = cons$a(?v1, ?v2)))
tff(axiom470,axiom,
    ! [A__questionmark_v0: 'A_constr_list$'] :
      ( ( A__questionmark_v0 != 'nil$a' )
    <=> ? [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$'] : ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ((((?v0 = nil$) ⇒ false) ∧ (∀ ?v1:A_TESL_atomic$ ((?v0 = cons$(?v1, nil$)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic_list$ ((?v0 = cons$(?v1, cons$(?v2, ?v3))) ⇒ false))) ⇒ false)
tff(axiom471,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$' )
         => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$'] :
            ( ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,'nil$') )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,'cons$'(A__questionmark_v2,A__questionmark_v3)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list$ ((((?v0 = nil$a) ⇒ false) ∧ (∀ ?v1:A_constr$ ((?v0 = cons$a(?v1, nil$a)) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr$ ?v3:A_constr_list$ ((?v0 = cons$a(?v1, cons$a(?v2, ?v3))) ⇒ false))) ⇒ false)
tff(axiom472,axiom,
    ! [A__questionmark_v0: 'A_constr_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$a' )
         => $false )
        & ! [A__questionmark_v1: 'A_constr$'] :
            ( ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,'nil$a') )
           => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr$',A__questionmark_v3: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,'cons$a'(A__questionmark_v2,A__questionmark_v3)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ((((?v0 = nil$) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ((?v0 = cons$(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom473,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$' )
         => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list$ ((((?v0 = nil$a) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr_list$ ((?v0 = cons$a(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom474,axiom,
    ! [A__questionmark_v0: 'A_constr_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$a' )
         => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ((?v0 = cons$(?v1, ?v2)) ⇒ ¬(?v0 = nil$))
tff(axiom475,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
      ( ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,A__questionmark_v2) )
     => ( A__questionmark_v0 != 'nil$' ) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:A_constr$ ?v2:A_constr_list$ ((?v0 = cons$a(?v1, ?v2)) ⇒ ¬(?v0 = nil$a))
tff(axiom476,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$'] :
      ( ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,A__questionmark_v2) )
     => ( A__questionmark_v0 != 'nil$a' ) ) ).

%% ∀ ?v0:A_TESL_atomic$ ?v1:A_TESL_atomic_list$ ¬(nil$ = cons$(?v0, ?v1))
tff(axiom477,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic$',A__questionmark_v1: 'A_TESL_atomic_list$'] : ( 'nil$' != 'cons$'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:A_constr$ ?v1:A_constr_list$ ¬(nil$a = cons$a(?v0, ?v1))
tff(axiom478,axiom,
    ! [A__questionmark_v0: 'A_constr$',A__questionmark_v1: 'A_constr_list$'] : ( 'nil$a' != 'cons$a'(A__questionmark_v0,A__questionmark_v1) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Cnt_expr$ ?v3:Cnt_expr$ ?v4:Nat_nat_prod_bool_fun$ ¬(ticks$(?v0, ?v1) = tickCntArith$(?v2, ?v3, ?v4))
tff(axiom479,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Cnt_expr$',A__questionmark_v3: 'Cnt_expr$',A__questionmark_v4: 'Nat_nat_prod_bool_fun$'] : ( 'ticks$'(A__questionmark_v0,A__questionmark_v1) != 'tickCntArith$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:A_tag_const$ ?v3:Cnt_expr$ ?v4:Cnt_expr$ ?v5:Nat_nat_prod_bool_fun$ ¬(timestamp$(?v0, ?v1, ?v2) = tickCntArith$(?v3, ?v4, ?v5))
tff(axiom480,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_tag_const$',A__questionmark_v3: 'Cnt_expr$',A__questionmark_v4: 'Cnt_expr$',A__questionmark_v5: 'Nat_nat_prod_bool_fun$'] : ( 'timestamp$'(A__questionmark_v0,A__questionmark_v1,A__questionmark_v2) != 'tickCntArith$'(A__questionmark_v3,A__questionmark_v4,A__questionmark_v5) ) ).

%% ∀ ?v0:Nat$ (fun_app$s(tESL_interpretation_stepwise$(nil$), ?v0) = collect$(uuk$))
tff(axiom481,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$s'('tESL_interpretation_stepwise$'('nil$'),A__questionmark_v0) = 'collect$'('uuk$') ) ).

%% ∀ ?v0:A_constr_list_a_constr_list_prod$ ((∀ ?v1:A_constr_list$ ((?v0 = pair$g(nil$a, ?v1)) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr_list$ ?v3:A_constr_list$ ((?v0 = pair$g(cons$a(?v1, ?v2), ?v3)) ⇒ false)) ⇒ false)
tff(axiom482,axiom,
    ! [A__questionmark_v0: 'A_constr_list_a_constr_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$g'('nil$a',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$g'('cons$a'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((∀ ?v1:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, nil$), ?v1)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, cons$(?v1, ?v2)), ?v3)) ⇒ false)) ⇒ false)
tff(axiom483,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a','cons$'(A__questionmark_v1,A__questionmark_v2)),A__questionmark_v3) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list_a_constr_list_prod$ ((∀ ?v1:A_constr_list$ ((?v0 = pair$g(nil$a, ?v1)) ⇒ false) ∧ (∀ ?v1:A_constr_list$ ((?v0 = pair$g(?v1, nil$a)) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr_list$ ?v3:A_constr$ ?v4:A_constr_list$ ((?v0 = pair$g(cons$a(?v1, ?v2), cons$a(?v3, ?v4))) ⇒ false))) ⇒ false)
tff(axiom484,axiom,
    ! [A__questionmark_v0: 'A_constr_list_a_constr_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$g'('nil$a',A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$g'(A__questionmark_v1,'nil$a') )
           => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'A_constr$',A__questionmark_v4: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'pair$g'('cons$a'(A__questionmark_v1,A__questionmark_v2),'cons$a'(A__questionmark_v3,A__questionmark_v4)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod$ ((∀ ?v1:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, nil$), ?v1)) ⇒ false) ∧ (∀ ?v1:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, ?v1), nil$)) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic$ ?v4:A_TESL_atomic_list$ ((?v0 = fun_app$g(fun_app$h(pair$a, cons$(?v1, ?v2)), cons$(?v3, ?v4))) ⇒ false))) ⇒ false)
tff(axiom485,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v1) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v1),'nil$') )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'fun_app$g'('fun_app$h'('pair$a','cons$'(A__questionmark_v1,A__questionmark_v2)),'cons$'(A__questionmark_v3,A__questionmark_v4)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_TESL_atomic_a_TESL_atomic_fun_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ ((∀ ?v1:A_TESL_atomic_a_TESL_atomic_fun$ ?v2:A_TESL_atomic_list$ ((?v0 = pair$h(?v1, fun_app$g(fun_app$h(pair$a, nil$), ?v2))) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic_a_TESL_atomic_fun$ ?v2:A_TESL_atomic$ ?v3:A_TESL_atomic_list$ ?v4:A_TESL_atomic_list$ ((?v0 = pair$h(?v1, fun_app$g(fun_app$h(pair$a, cons$(?v2, ?v3)), ?v4))) ⇒ false)) ⇒ false)
tff(axiom486,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_a_TESL_atomic_fun_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( ( ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_fun$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'pair$h'(A__questionmark_v1,'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v2)) )
           => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic_a_TESL_atomic_fun$',A__questionmark_v2: 'A_TESL_atomic$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'pair$h'(A__questionmark_v1,'fun_app$g'('fun_app$h'('pair$a','cons$'(A__questionmark_v2,A__questionmark_v3)),A__questionmark_v4)) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$a(fun_app$b(bot$c, ?v0), ?v1) = member$a(fun_app$c(fun_app$d(pair$, ?v0), ?v1), bot$))
tff(axiom487,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$a'('fun_app$b'('bot$c',A__questionmark_v0),A__questionmark_v1)
    <=> 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),A__questionmark_v1),'bot$') ) ).

%% ∀ ?v0:Nat$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$i(fun_app$j(bot$d, ?v0), ?v1) = member$c(fun_app$k(fun_app$l(pair$b, ?v0), ?v1), bot$e))
tff(axiom488,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$i'('fun_app$j'('bot$d',A__questionmark_v0),A__questionmark_v1)
    <=> 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v0),A__questionmark_v1),'bot$e') ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ?v1:A_TESL_atomic_list$ (fun_app$e(fun_app$f(bot$f, ?v0), ?v1) = member$b(fun_app$g(fun_app$h(pair$a, ?v0), ?v1), bot$g))
tff(axiom489,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$',A__questionmark_v1: 'A_TESL_atomic_list$'] :
      ( 'fun_app$e'('fun_app$f'('bot$f',A__questionmark_v0),A__questionmark_v1)
    <=> 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v0),A__questionmark_v1),'bot$g') ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:A_tag_const$ ?v4:Clock$ ?v5:A_TESL_atomic_list$ ?v6:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(sporadicOn$(?v2, ?v3, ?v4), ?v5)), ?v6)))), fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v2, ?v1), cons$a(timestamp$(?v4, ?v1, ?v3), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v5), ?v6))))
tff(axiom490,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'A_tag_const$',A__questionmark_v4: 'Clock$',A__questionmark_v5: 'A_TESL_atomic_list$',A__questionmark_v6: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('sporadicOn$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4),A__questionmark_v5)),A__questionmark_v6)))),'fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v2,A__questionmark_v1),'cons$a'('timestamp$'(A__questionmark_v4,A__questionmark_v1,A__questionmark_v3),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v5),A__questionmark_v6)))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, nil$), ?v2)))) = heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, fun_app$t(nat$, (fun_app$u(of_nat$, ?v1) + 1))), fun_app$g(fun_app$h(pair$a, ?v2), nil$)))))
tff(axiom491,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v2)))) = 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b','fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),'nil$')))) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ((fun_app$v(operational_semantics_intro$(?v0), ?v1) ∧ ∀ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ (((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, nil$), ?v4)))) ∧ (?v1 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1))), fun_app$g(fun_app$h(pair$a, ?v4), nil$))))) ⇒ false)) ⇒ false)
tff(axiom492,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( ( 'fun_app$v'('operational_semantics_intro$'(A__questionmark_v0),A__questionmark_v1)
        & ! [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
            ( ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v4))) )
              & ( A__questionmark_v1 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b','fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'nil$'))) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$ (fun_app$v(operational_semantics_intro$(?v0), ?v1) = ∃ ?v2:A_constr_list$ ?v3:Nat$ ?v4:A_TESL_atomic_list$ ((?v0 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v3), fun_app$g(fun_app$h(pair$a, nil$), ?v4)))) ∧ (?v1 = fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, fun_app$t(nat$, (fun_app$u(of_nat$, ?v3) + 1))), fun_app$g(fun_app$h(pair$a, ?v4), nil$))))))
tff(axiom493,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod$'] :
      ( 'fun_app$v'('operational_semantics_intro$'(A__questionmark_v0),A__questionmark_v1)
    <=> ? [A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat$',A__questionmark_v4: 'A_TESL_atomic_list$'] :
          ( ( A__questionmark_v0 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v3),'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v4))) )
          & ( A__questionmark_v1 = 'fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b','fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v3),1))),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'nil$'))) ) ) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:A_TESL_atomic_list$ fun_app$v(operational_semantics_intro$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, nil$), ?v2)))), fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, fun_app$t(nat$, (fun_app$u(of_nat$, ?v1) + 1))), fun_app$g(fun_app$h(pair$a, ?v2), nil$))))
tff(axiom494,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_intro$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','nil$'),A__questionmark_v2)))),'fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b','fun_app$t'('nat$',$sum('fun_app$u'('of_nat$',A__questionmark_v1),1))),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),'nil$')))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:A_tag_const$ ?v4:Clock$ ?v5:A_TESL_atomic_list$ ?v6:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(sporadicOn$(?v2, ?v3, ?v4), ?v5)), ?v6)))) = fun_app$q(fun_app$r(sup$, heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v5), cons$(sporadicOn$(?v2, ?v3, ?v4), ?v6)))))), heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v2, ?v1), cons$a(timestamp$(?v4, ?v1, ?v3), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v5), ?v6))))))
tff(axiom495,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'A_tag_const$',A__questionmark_v4: 'Clock$',A__questionmark_v5: 'A_TESL_atomic_list$',A__questionmark_v6: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('sporadicOn$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4),A__questionmark_v5)),A__questionmark_v6)))) = 'fun_app$q'('fun_app$r'('sup$','heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v5),'cons$'('sporadicOn$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4),A__questionmark_v6)))))),'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v2,A__questionmark_v1),'cons$a'('timestamp$'(A__questionmark_v4,A__questionmark_v1,A__questionmark_v3),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v5),A__questionmark_v6))))) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(implies$(?v2, ?v3), ?v4)), ?v5)))), fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v2, ?v1), cons$a(ticks$(?v3, ?v1), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(implies$(?v2, ?v3), ?v5)))))
tff(axiom496,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v2,A__questionmark_v1),'cons$a'('ticks$'(A__questionmark_v3,A__questionmark_v1),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v1), ?v2) = (less_eq$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)))
tff(axiom497,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v2)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)), ?v2) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)))
tff(axiom498,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2)
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) ≤ ?v2) = ((?v0 ≤ ?v2) ∧ (?v1 ≤ ?v2)))
tff(axiom499,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v2)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v1), ?v2) = (less_eq$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)))
tff(axiom500,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v2)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)), ?v2) = (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)))
tff(axiom501,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2)
    <=> ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) ≤ ?v2) = ((?v0 ≤ ?v2) ∧ (?v1 ≤ ?v2)))
tff(axiom502,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( $lesseq(A__questionmark_v0,A__questionmark_v2)
        & $lesseq(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = ?v0)
tff(axiom503,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v0), ?v1)) = ?v0)
tff(axiom504,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v1), ?v2) = (less_eq$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)))
tff(axiom505,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
    <=> ( 'less_eq$'(A__questionmark_v0,A__questionmark_v2)
        & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), ?v0) = ?v0)
tff(axiom506,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), ?v1) = ?v1)
tff(axiom507,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = A__questionmark_v1 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v0), ?v1)) = ?v0)
tff(axiom508,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v0)) = ?v0)
tff(axiom509,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v0) = ?v0)
tff(axiom510,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v0) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v1) = ?v1)
tff(axiom511,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v1) = A__questionmark_v1 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v0), ?v1)) = ?v0)
tff(axiom512,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v0)) = ?v0)
tff(axiom513,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:A_constr_list$ ((((?v0 = nil$a) ⇒ false) ∧ ∀ ?v1:A_constr$ ?v2:A_constr_list$ ((?v0 = cons$a(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom514,axiom,
    ! [A__questionmark_v0: 'A_constr_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$a' )
         => $false )
        & ! [A__questionmark_v1: 'A_constr$',A__questionmark_v2: 'A_constr_list$'] :
            ( ( A__questionmark_v0 = 'cons$a'(A__questionmark_v1,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Clock$ ?v1:Clock$ ?v2:Clock$ ?v3:Clock$ ¬(implies$(?v0, ?v1) = weaklyPrecedes$(?v2, ?v3))
tff(axiom515,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Clock$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$'] : ( 'implies$'(A__questionmark_v0,A__questionmark_v1) != 'weaklyPrecedes$'(A__questionmark_v2,A__questionmark_v3) ) ).

%% (symbolic_run_interpretation$(nil$a) = collect$(uuk$))
tff(axiom516,axiom,
    'symbolic_run_interpretation$'('nil$a') = 'collect$'('uuk$') ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v2)), fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom517,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v0), ?v2)))
tff(axiom518,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v2)), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom519,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2)) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom520,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (∀ ?v3:A_run_set$ ?v4:A_run_set$ ?v5:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v3), fun_app$q(fun_app$r(inf$, ?v4), ?v5)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v3), ?v4)), fun_app$q(fun_app$r(sup$, ?v3), ?v5))) ⇒ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2)) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v0), ?v2))))
tff(axiom521,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v3),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v4),A__questionmark_v5)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v3),A__questionmark_v4)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v3),A__questionmark_v5)) )
     => ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (∀ ?v3:A_run_set$ ?v4:A_run_set$ ?v5:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v3), fun_app$q(fun_app$r(sup$, ?v4), ?v5)) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v3), ?v4)), fun_app$q(fun_app$r(inf$, ?v3), ?v5))) ⇒ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v0), ?v2))))
tff(axiom522,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v3),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v4),A__questionmark_v5)) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v3),A__questionmark_v4)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v3),A__questionmark_v5)) )
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v2)), fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom523,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v2)), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom524,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v0), ?v2)))
tff(axiom525,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2)) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom526,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v2)), fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom527,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v2)), fun_app$q(fun_app$r(inf$, ?v1), ?v2)))
tff(axiom528,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v0), ?v2)))
tff(axiom529,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2)) = fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v0), ?v2)))
tff(axiom530,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) = 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v1), ?v2))), fun_app$q(fun_app$r(inf$, ?v2), ?v0)) = fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v1), ?v2))), fun_app$q(fun_app$r(sup$, ?v2), ?v0)))
tff(axiom531,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2))),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v2),A__questionmark_v0)) = 'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2))),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v2),A__questionmark_v0)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), fun_app$q(fun_app$r(sup$, ?v1), ?v3)))
tff(axiom532,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v1)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), ?v1))
tff(axiom533,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v0), ?v1))
tff(axiom534,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v0))
tff(axiom535,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom536,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v1), ?v0) = ?v1))
tff(axiom537,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v2)) ∧ ∀ ?v3:A_run_set$ ?v4:A_run_set$ ((less_eq$(?v3, ?v1) ∧ (less_eq$(?v4, ?v2) ∧ (?v0 = fun_app$q(fun_app$r(sup$, ?v3), ?v4)))) ⇒ false)) ⇒ false)
tff(axiom538,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2))
        & ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$'] :
            ( ( 'less_eq$'(A__questionmark_v3,A__questionmark_v1)
              & 'less_eq$'(A__questionmark_v4,A__questionmark_v2)
              & ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v3),A__questionmark_v4) ) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom539,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v0))
tff(axiom540,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0))
tff(axiom541,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0))
tff(axiom542,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v0), ?v1))
tff(axiom543,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1))
tff(axiom544,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1))
tff(axiom545,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v1), ?v2) ∧ ((less_eq$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom546,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
        & ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v2)
            & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)), ?v2) ∧ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ false)) ⇒ false)
tff(axiom547,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2)
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) ≤ ?v2) ∧ (((?v0 ≤ ?v2) ∧ (?v1 ≤ ?v2)) ⇒ false)) ⇒ false)
tff(axiom548,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
        & ( ( $lesseq(A__questionmark_v0,A__questionmark_v2)
            & $lesseq(A__questionmark_v1,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v1)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), ?v1))
tff(axiom549,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)), ?v1))
tff(axiom550,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v1)) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2) ≤ ?v1))
tff(axiom551,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v1) )
     => $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v0), ?v1))
tff(axiom552,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1))
tff(axiom553,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1))
tff(axiom554,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v0))
tff(axiom555,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0))
tff(axiom556,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0))
tff(axiom557,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom558,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v2)))
tff(axiom559,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v2)))
tff(axiom560,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v2), ?v1)))
tff(axiom561,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v2), ?v1)))
tff(axiom562,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v2), ?v1)))
tff(axiom563,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), fun_app$q(fun_app$r(sup$, ?v1), ?v3)))
tff(axiom564,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v3)))
tff(axiom565,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2)),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v3)) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2) ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v3)))
tff(axiom566,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v3) )
     => $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2),'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ?v3:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), fun_app$q(fun_app$r(sup$, ?v1), ?v3)))
tff(axiom567,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$',A__questionmark_v3: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v3) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ?v3:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v3)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v3)))
tff(axiom568,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v3) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2)),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ?v3:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v3)) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2) ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v3)))
tff(axiom569,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int,A__questionmark_v3: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v3) )
     => $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2),'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v3)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v1)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), ?v1))
tff(axiom570,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)), ?v1))
tff(axiom571,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v1)) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2) ≤ ?v1))
tff(axiom572,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v1) )
     => $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom573,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1) = ?v1))
tff(axiom574,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) = ?v1))
tff(axiom575,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((less_eq$(?v0, ?v1) ∧ ((?v1 = fun_app$q(fun_app$r(sup$, ?v1), ?v0)) ⇒ false)) ⇒ false)
tff(axiom576,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & ( ( A__questionmark_v1 = 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ ((?v1 = fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0)) ⇒ false)) ⇒ false)
tff(axiom577,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & ( ( A__questionmark_v1 = 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int (((?v0 ≤ ?v1) ∧ ((?v1 = fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0)) ⇒ false)) ⇒ false)
tff(axiom578,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & ( ( A__questionmark_v1 = 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ((?v0 = fun_app$q(fun_app$r(sup$, ?v0), ?v1)) ⇒ less_eq$(?v1, ?v0))
tff(axiom579,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( ( A__questionmark_v0 = 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) )
     => 'less_eq$'(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ((?v0 = fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v0))
tff(axiom580,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( ( A__questionmark_v0 = 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1) )
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v0) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 = fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1)) ⇒ (?v1 ≤ ?v0))
tff(axiom581,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( ( A__questionmark_v0 = 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1) )
     => $lesseq(A__questionmark_v1,A__questionmark_v0) ) ).

%% ∀ ?v0:A_run_set_a_run_set_a_run_set_fun_fun$ ?v1:A_run_set$ ?v2:A_run_set$ ((∀ ?v3:A_run_set$ ?v4:A_run_set$ less_eq$(?v3, fun_app$q(fun_app$r(?v0, ?v3), ?v4)) ∧ (∀ ?v3:A_run_set$ ?v4:A_run_set$ less_eq$(?v4, fun_app$q(fun_app$r(?v0, ?v3), ?v4)) ∧ ∀ ?v3:A_run_set$ ?v4:A_run_set$ ?v5:A_run_set$ ((less_eq$(?v4, ?v3) ∧ less_eq$(?v5, ?v3)) ⇒ less_eq$(fun_app$q(fun_app$r(?v0, ?v4), ?v5), ?v3)))) ⇒ (fun_app$q(fun_app$r(sup$, ?v1), ?v2) = fun_app$q(fun_app$r(?v0, ?v1), ?v2)))
tff(axiom582,axiom,
    ! [A__questionmark_v0: 'A_run_set_a_run_set_a_run_set_fun_fun$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$'] : 'less_eq$'(A__questionmark_v3,'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$'] : 'less_eq$'(A__questionmark_v4,'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: 'A_run_set$',A__questionmark_v4: 'A_run_set$',A__questionmark_v5: 'A_run_set$'] :
            ( ( 'less_eq$'(A__questionmark_v4,A__questionmark_v3)
              & 'less_eq$'(A__questionmark_v5,A__questionmark_v3) )
           => 'less_eq$'('fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5),A__questionmark_v3) ) )
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2) = 'fun_app$q'('fun_app$r'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Nat_nat_nat_fun_fun$ ?v1:Nat$ ?v2:Nat$ ((∀ ?v3:Nat$ ?v4:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v3), fun_app$aa(fun_app$ab(?v0, ?v3), ?v4)) ∧ (∀ ?v3:Nat$ ?v4:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v4), fun_app$aa(fun_app$ab(?v0, ?v3), ?v4)) ∧ ∀ ?v3:Nat$ ?v4:Nat$ ?v5:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v4), ?v3) ∧ fun_app$m(fun_app$n(less_eq$f, ?v5), ?v3)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(?v0, ?v4), ?v5)), ?v3)))) ⇒ (fun_app$aa(fun_app$ab(sup$a, ?v1), ?v2) = fun_app$aa(fun_app$ab(?v0, ?v1), ?v2)))
tff(axiom583,axiom,
    ! [A__questionmark_v0: 'Nat_nat_nat_fun_fun$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v3),'fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),'fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: 'Nat$',A__questionmark_v4: 'Nat$',A__questionmark_v5: 'Nat$'] :
            ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v4),A__questionmark_v3)
              & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v5),A__questionmark_v3) )
           => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)),A__questionmark_v3) ) )
     => ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v2) = 'fun_app$aa'('fun_app$ab'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:Int_int_int_fun_fun$ ?v1:Int ?v2:Int ((∀ ?v3:Int ?v4:Int (?v3 ≤ fun_app$ac(fun_app$ad(?v0, ?v3), ?v4)) ∧ (∀ ?v3:Int ?v4:Int (?v4 ≤ fun_app$ac(fun_app$ad(?v0, ?v3), ?v4)) ∧ ∀ ?v3:Int ?v4:Int ?v5:Int (((?v4 ≤ ?v3) ∧ (?v5 ≤ ?v3)) ⇒ (fun_app$ac(fun_app$ad(?v0, ?v4), ?v5) ≤ ?v3)))) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v1), ?v2) = fun_app$ac(fun_app$ad(?v0, ?v1), ?v2)))
tff(axiom584,axiom,
    ! [A__questionmark_v0: 'Int_int_int_fun_fun$',A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( ! [A__questionmark_v3: $int,A__questionmark_v4: $int] : $lesseq(A__questionmark_v3,'fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int] : $lesseq(A__questionmark_v4,'fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v3),A__questionmark_v4))
        & ! [A__questionmark_v3: $int,A__questionmark_v4: $int,A__questionmark_v5: $int] :
            ( ( $lesseq(A__questionmark_v4,A__questionmark_v3)
              & $lesseq(A__questionmark_v5,A__questionmark_v3) )
           => $lesseq('fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5),A__questionmark_v3) ) )
     => ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v2) = 'fun_app$ac'('fun_app$ad'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v1), ?v0) = ?v1))
tff(axiom585,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0) = ?v1))
tff(axiom586,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0) = ?v1))
tff(axiom587,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom588,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1) = ?v1))
tff(axiom589,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) = ?v1))
tff(axiom590,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v1), ?v0) = ?v1))
tff(axiom591,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0) = ?v1))
tff(axiom592,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0) = ?v1))
tff(axiom593,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) ⇒ (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom594,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ (fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1) = ?v1))
tff(axiom595,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) = ?v1))
tff(axiom596,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v1), ?v2) ∧ ((less_eq$(?v0, ?v2) ∧ less_eq$(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom597,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
        & ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v2)
            & 'less_eq$'(A__questionmark_v1,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)), ?v2) ∧ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v2) ∧ fun_app$m(fun_app$n(less_eq$f, ?v1), ?v2)) ⇒ false)) ⇒ false)
tff(axiom598,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2)
        & ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v2)
            & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v1),A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) ≤ ?v2) ∧ (((?v0 ≤ ?v2) ∧ (?v1 ≤ ?v2)) ⇒ false)) ⇒ false)
tff(axiom599,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1),A__questionmark_v2)
        & ( ( $lesseq(A__questionmark_v0,A__questionmark_v2)
            & $lesseq(A__questionmark_v1,A__questionmark_v2) )
         => $false ) )
     => $false ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((less_eq$(?v0, ?v1) ∧ less_eq$(?v2, ?v1)) ⇒ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), ?v2), ?v1))
tff(axiom600,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
        & 'less_eq$'(A__questionmark_v2,A__questionmark_v1) )
     => 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ ((fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ∧ fun_app$m(fun_app$n(less_eq$f, ?v2), ?v1)) ⇒ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)), ?v1))
tff(axiom601,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
        & 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v2),A__questionmark_v1) )
     => 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2)),A__questionmark_v1) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (((?v0 ≤ ?v1) ∧ (?v2 ≤ ?v1)) ⇒ (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2) ≤ ?v1))
tff(axiom602,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( ( $lesseq(A__questionmark_v0,A__questionmark_v1)
        & $lesseq(A__questionmark_v2,A__questionmark_v1) )
     => $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2),A__questionmark_v1) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (?v1 = fun_app$q(fun_app$r(sup$, ?v1), ?v0)))
tff(axiom603,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( A__questionmark_v1 = 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (?v1 = fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0)))
tff(axiom604,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( A__questionmark_v1 = 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (?v1 = fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0)))
tff(axiom605,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( A__questionmark_v1 = 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0) ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v0), ?v1))
tff(axiom606,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1))
tff(axiom607,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1))
tff(axiom608,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v0))
tff(axiom609,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] : 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0))
tff(axiom610,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:Int ?v1:Int (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0))
tff(axiom611,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] : $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0)) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(sup$, ?v1), ?v0) = ?v1))
tff(axiom612,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(sup$a, ?v1), ?v0) = ?v1))
tff(axiom613,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(sup$b, ?v1), ?v0) = ?v1))
tff(axiom614,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v0) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ (less_eq$(?v0, ?v1) = (fun_app$q(fun_app$r(sup$, ?v0), ?v1) = ?v1))
tff(axiom615,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) = (fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1) = ?v1))
tff(axiom616,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
    <=> ( 'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:Int ?v1:Int ((?v0 ≤ ?v1) = (fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1) = ?v1))
tff(axiom617,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
    <=> ( 'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1) = A__questionmark_v1 ) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom618,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v2)))
tff(axiom619,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v1), ?v2)))
tff(axiom620,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v2)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ (less_eq$(?v0, ?v1) ⇒ less_eq$(?v0, fun_app$q(fun_app$r(sup$, ?v2), ?v1)))
tff(axiom621,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( 'less_eq$'(A__questionmark_v0,A__questionmark_v1)
     => 'less_eq$'(A__questionmark_v0,'fun_app$q'('fun_app$r'('sup$',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ (fun_app$m(fun_app$n(less_eq$f, ?v0), ?v1) ⇒ fun_app$m(fun_app$n(less_eq$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v2), ?v1)))
tff(axiom622,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] :
      ( 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),A__questionmark_v1)
     => 'fun_app$m'('fun_app$n'('less_eq$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int ((?v0 ≤ ?v1) ⇒ (?v0 ≤ fun_app$ac(fun_app$ad(sup$b, ?v2), ?v1)))
tff(axiom623,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] :
      ( $lesseq(A__questionmark_v0,A__questionmark_v1)
     => $lesseq(A__questionmark_v0,'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v2),A__questionmark_v1)) ) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ less_eq$(fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), fun_app$q(fun_app$r(inf$, ?v0), ?v2)), fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2)))
tff(axiom624,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2))) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, fun_app$aa(fun_app$ab(inf$f, ?v0), ?v1)), fun_app$aa(fun_app$ab(inf$f, ?v0), ?v2))), fun_app$aa(fun_app$ab(inf$f, ?v0), fun_app$aa(fun_app$ab(sup$a, ?v1), ?v2)))
tff(axiom625,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a','fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v1)),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),A__questionmark_v2))),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v1),A__questionmark_v2))) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (fun_app$ac(fun_app$ad(sup$b, fun_app$ac(fun_app$ad(inf$g, ?v0), ?v1)), fun_app$ac(fun_app$ad(inf$g, ?v0), ?v2)) ≤ fun_app$ac(fun_app$ad(inf$g, ?v0), fun_app$ac(fun_app$ad(sup$b, ?v1), ?v2)))
tff(axiom626,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : $lesseq('fun_app$ac'('fun_app$ad'('sup$b','fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v1)),'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),A__questionmark_v2)),'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v0),'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v1),A__questionmark_v2))) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ less_eq$(fun_app$q(fun_app$r(sup$, ?v0), fun_app$q(fun_app$r(inf$, ?v1), ?v2)), fun_app$q(fun_app$r(inf$, fun_app$q(fun_app$r(sup$, ?v0), ?v1)), fun_app$q(fun_app$r(sup$, ?v0), ?v2)))
tff(axiom627,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] : 'less_eq$'('fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),'fun_app$q'('fun_app$r'('inf$',A__questionmark_v1),A__questionmark_v2)),'fun_app$q'('fun_app$r'('inf$','fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v1)),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v0),A__questionmark_v2))) ).

%% ∀ ?v0:Nat$ ?v1:Nat$ ?v2:Nat$ fun_app$m(fun_app$n(less_eq$f, fun_app$aa(fun_app$ab(sup$a, ?v0), fun_app$aa(fun_app$ab(inf$f, ?v1), ?v2))), fun_app$aa(fun_app$ab(inf$f, fun_app$aa(fun_app$ab(sup$a, ?v0), ?v1)), fun_app$aa(fun_app$ab(sup$a, ?v0), ?v2)))
tff(axiom628,axiom,
    ! [A__questionmark_v0: 'Nat$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Nat$'] : 'fun_app$m'('fun_app$n'('less_eq$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),'fun_app$aa'('fun_app$ab'('inf$f',A__questionmark_v1),A__questionmark_v2))),'fun_app$aa'('fun_app$ab'('inf$f','fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v1)),'fun_app$aa'('fun_app$ab'('sup$a',A__questionmark_v0),A__questionmark_v2))) ).

%% ∀ ?v0:Int ?v1:Int ?v2:Int (fun_app$ac(fun_app$ad(sup$b, ?v0), fun_app$ac(fun_app$ad(inf$g, ?v1), ?v2)) ≤ fun_app$ac(fun_app$ad(inf$g, fun_app$ac(fun_app$ad(sup$b, ?v0), ?v1)), fun_app$ac(fun_app$ad(sup$b, ?v0), ?v2)))
tff(axiom629,axiom,
    ! [A__questionmark_v0: $int,A__questionmark_v1: $int,A__questionmark_v2: $int] : $lesseq('fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),'fun_app$ac'('fun_app$ad'('inf$g',A__questionmark_v1),A__questionmark_v2)),'fun_app$ac'('fun_app$ad'('inf$g','fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v1)),'fun_app$ac'('fun_app$ad'('sup$b',A__questionmark_v0),A__questionmark_v2))) ).

%% ∀ ?v0:A_run_set$ ?v1:A_run_set$ ?v2:A_run_set$ ((fun_app$q(fun_app$r(sup$, fun_app$q(fun_app$r(inf$, ?v0), ?v1)), ?v2) = fun_app$q(fun_app$r(inf$, ?v0), fun_app$q(fun_app$r(sup$, ?v1), ?v2))) = less_eq$(?v2, ?v0))
tff(axiom630,axiom,
    ! [A__questionmark_v0: 'A_run_set$',A__questionmark_v1: 'A_run_set$',A__questionmark_v2: 'A_run_set$'] :
      ( ( 'fun_app$q'('fun_app$r'('sup$','fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),A__questionmark_v1)),A__questionmark_v2) = 'fun_app$q'('fun_app$r'('inf$',A__questionmark_v0),'fun_app$q'('fun_app$r'('sup$',A__questionmark_v1),A__questionmark_v2)) )
    <=> 'less_eq$'(A__questionmark_v2,A__questionmark_v0) ) ).

%% ∀ ?v0:A_TESL_atomic_list$ ((((?v0 = nil$) ⇒ false) ∧ ∀ ?v1:A_TESL_atomic$ ?v2:A_TESL_atomic_list$ ((?v0 = cons$(?v1, ?v2)) ⇒ false)) ⇒ false)
tff(axiom631,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list$'] :
      ( ( ( ( A__questionmark_v0 = 'nil$' )
         => $false )
        & ! [A__questionmark_v1: 'A_TESL_atomic$',A__questionmark_v2: 'A_TESL_atomic_list$'] :
            ( ( A__questionmark_v0 = 'cons$'(A__questionmark_v1,A__questionmark_v2) )
           => $false ) )
     => $false ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:A_constr_list$ ?v3:A_TESL_atomic_list$ ?v4:Clock$ ?v5:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, cons$a(notTicks$(?v0, ?v1), ?v2)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v3), cons$(implies$(?v0, ?v4), ?v5)))), insert$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v0, ?v1), cons$a(ticks$(?v4, ?v1), ?v2))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v3), cons$(implies$(?v0, ?v4), ?v5)))), bot$)), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(implies$(?v0, ?v4), ?v3)), ?v5))))))
tff(axiom632,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'Clock$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('notTicks$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),'cons$'('implies$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)))),'insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v0,A__questionmark_v1),'cons$a'('ticks$'(A__questionmark_v4,A__questionmark_v1),A__questionmark_v2))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),'cons$'('implies$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)))),'bot$')),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('implies$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)),A__questionmark_v5)))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(implies$(?v2, ?v3), ?v4)), ?v5)))) = fun_app$q(fun_app$r(sup$, heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(notTicks$(?v2, ?v1), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(implies$(?v2, ?v3), ?v5)))))), heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v2, ?v1), cons$a(ticks$(?v3, ?v1), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(implies$(?v2, ?v3), ?v5)))))))
tff(axiom633,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))) = 'fun_app$q'('fun_app$r'('sup$','heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('notTicks$'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5)))))),'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v2,A__questionmark_v1),'cons$a'('ticks$'(A__questionmark_v3,A__questionmark_v1),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5)))))) ) ).

%% ∀ ?v0:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v1:A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$ ?v2:A_constr_list$ ?v3:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$ (fun_app$a(fun_app$b(sup$c(uuh$(?v0), uuh$(?v1)), ?v2), ?v3) = member$a(fun_app$c(fun_app$d(pair$, ?v2), ?v3), sup$d(?v0, ?v1)))
tff(axiom634,axiom,
    ! [A__questionmark_v0: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v1: 'A_constr_list_nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_prod_set$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod$'] :
      ( 'fun_app$a'('fun_app$b'('sup$c'('uuh$'(A__questionmark_v0),'uuh$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$a'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),A__questionmark_v3),'sup$d'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v1:Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$ ?v2:Nat$ ?v3:A_TESL_atomic_list_a_TESL_atomic_list_prod$ (fun_app$i(fun_app$j(sup$e(uui$(?v0), uui$(?v1)), ?v2), ?v3) = member$c(fun_app$k(fun_app$l(pair$b, ?v2), ?v3), sup$f(?v0, ?v1)))
tff(axiom635,axiom,
    ! [A__questionmark_v0: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v1: 'Nat_a_TESL_atomic_list_a_TESL_atomic_list_prod_prod_set$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'A_TESL_atomic_list_a_TESL_atomic_list_prod$'] :
      ( 'fun_app$i'('fun_app$j'('sup$e'('uui$'(A__questionmark_v0),'uui$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$c'('fun_app$k'('fun_app$l'('pair$b',A__questionmark_v2),A__questionmark_v3),'sup$f'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v1:A_TESL_atomic_list_a_TESL_atomic_list_prod_set$ ?v2:A_TESL_atomic_list$ ?v3:A_TESL_atomic_list$ (fun_app$e(fun_app$f(sup$g(uuj$(?v0), uuj$(?v1)), ?v2), ?v3) = member$b(fun_app$g(fun_app$h(pair$a, ?v2), ?v3), sup$h(?v0, ?v1)))
tff(axiom636,axiom,
    ! [A__questionmark_v0: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v1: 'A_TESL_atomic_list_a_TESL_atomic_list_prod_set$',A__questionmark_v2: 'A_TESL_atomic_list$',A__questionmark_v3: 'A_TESL_atomic_list$'] :
      ( 'fun_app$e'('fun_app$f'('sup$g'('uuj$'(A__questionmark_v0),'uuj$'(A__questionmark_v1)),A__questionmark_v2),A__questionmark_v3)
    <=> 'member$b'('fun_app$g'('fun_app$h'('pair$a',A__questionmark_v2),A__questionmark_v3),'sup$h'(A__questionmark_v0,A__questionmark_v1)) ) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:Cnt_expr$ ?v3:Cnt_expr$ ?v4:Nat_nat_prod_bool_fun$ ¬(notTicks$(?v0, ?v1) = tickCntArith$(?v2, ?v3, ?v4))
tff(axiom637,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Cnt_expr$',A__questionmark_v3: 'Cnt_expr$',A__questionmark_v4: 'Nat_nat_prod_bool_fun$'] : ( 'notTicks$'(A__questionmark_v0,A__questionmark_v1) != 'tickCntArith$'(A__questionmark_v2,A__questionmark_v3,A__questionmark_v4) ) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ fun_app$v(operational_semantics_elim$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(implies$(?v2, ?v3), ?v4)), ?v5)))), fun_app$c(fun_app$d(pair$, cons$a(notTicks$(?v2, ?v1), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(implies$(?v2, ?v3), ?v5)))))
tff(axiom638,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'fun_app$v'('operational_semantics_elim$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))),'fun_app$c'('fun_app$d'('pair$','cons$a'('notTicks$'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('implies$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5))))) ).

%% ∀ ?v0:Clock$ ?v1:Nat$ ?v2:A_constr_list$ ?v3:A_TESL_atomic_list$ ?v4:Clock$ ?v5:A_TESL_atomic_list$ less_eq$i(insert$(fun_app$c(fun_app$d(pair$, cons$a(notTicks$(?v0, ?v1), ?v2)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v3), cons$(impliesNot$(?v0, ?v4), ?v5)))), insert$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v0, ?v1), cons$a(notTicks$(?v4, ?v1), ?v2))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v3), cons$(impliesNot$(?v0, ?v4), ?v5)))), bot$)), collect$b(operational_semantics_step$(fun_app$c(fun_app$d(pair$, ?v2), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(impliesNot$(?v0, ?v4), ?v3)), ?v5))))))
tff(axiom639,axiom,
    ! [A__questionmark_v0: 'Clock$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'A_constr_list$',A__questionmark_v3: 'A_TESL_atomic_list$',A__questionmark_v4: 'Clock$',A__questionmark_v5: 'A_TESL_atomic_list$'] : 'less_eq$i'('insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('notTicks$'(A__questionmark_v0,A__questionmark_v1),A__questionmark_v2)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),'cons$'('impliesNot$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)))),'insert$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v0,A__questionmark_v1),'cons$a'('notTicks$'(A__questionmark_v4,A__questionmark_v1),A__questionmark_v2))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v3),'cons$'('impliesNot$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v5)))),'bot$')),'collect$b'('operational_semantics_step$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v2),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('impliesNot$'(A__questionmark_v0,A__questionmark_v4),A__questionmark_v3)),A__questionmark_v5)))))) ).

%% ∀ ?v0:A_constr_list$ ?v1:Nat$ ?v2:Clock$ ?v3:Clock$ ?v4:A_TESL_atomic_list$ ?v5:A_TESL_atomic_list$ (heronConf_interpretation$(fun_app$c(fun_app$d(pair$, ?v0), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, cons$(impliesNot$(?v2, ?v3), ?v4)), ?v5)))) = fun_app$q(fun_app$r(sup$, heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(notTicks$(?v2, ?v1), ?v0)), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(impliesNot$(?v2, ?v3), ?v5)))))), heronConf_interpretation$(fun_app$c(fun_app$d(pair$, cons$a(ticks$(?v2, ?v1), cons$a(notTicks$(?v3, ?v1), ?v0))), fun_app$k(fun_app$l(pair$b, ?v1), fun_app$g(fun_app$h(pair$a, ?v4), cons$(impliesNot$(?v2, ?v3), ?v5)))))))
tff(axiom640,axiom,
    ! [A__questionmark_v0: 'A_constr_list$',A__questionmark_v1: 'Nat$',A__questionmark_v2: 'Clock$',A__questionmark_v3: 'Clock$',A__questionmark_v4: 'A_TESL_atomic_list$',A__questionmark_v5: 'A_TESL_atomic_list$'] : ( 'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$',A__questionmark_v0),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a','cons$'('impliesNot$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v4)),A__questionmark_v5)))) = 'fun_app$q'('fun_app$r'('sup$','heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('notTicks$'(A__questionmark_v2,A__questionmark_v1),A__questionmark_v0)),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('impliesNot$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5)))))),'heronConf_interpretation$'('fun_app$c'('fun_app$d'('pair$','cons$a'('ticks$'(A__questionmark_v2,A__questionmark_v1),'cons$a'('notTicks$'(A__questionmark_v3,A__questionmark_v1),A__questionmark_v0))),'fun_app$k'('fun_app$l'('pair$b',A__questionmark_v1),'fun_app$g'('fun_app$h'('pair$a',A__questionmark_v4),'cons$'('impliesNot$'(A__questionmark_v2,A__questionmark_v3),A__questionmark_v5)))))) ) ).

%% ∀ ?v0:Nat$ (0 ≤ fun_app$u(of_nat$, ?v0))
tff(axiom641,axiom,
    ! [A__questionmark_v0: 'Nat$'] : $lesseq(0,'fun_app$u'('of_nat$',A__questionmark_v0)) ).

%% ∀ ?v0:Nat$ (fun_app$t(nat$, fun_app$u(of_nat$, ?v0)) = ?v0)
tff(axiom642,axiom,
    ! [A__questionmark_v0: 'Nat$'] : ( 'fun_app$t'('nat$','fun_app$u'('of_nat$',A__questionmark_v0)) = A__questionmark_v0 ) ).

%% ∀ ?v0:Int (fun_app$u(of_nat$, fun_app$t(nat$, ?v0)) = (if (0 ≤ ?v0) ?v0 else 0))
tff(axiom643,axiom,
    ! [A__questionmark_v0: $int] :
      ( ( $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$u'('of_nat$','fun_app$t'('nat$',A__questionmark_v0)) = A__questionmark_v0 ) )
      & ( ~ $lesseq(0,A__questionmark_v0)
       => ( 'fun_app$u'('of_nat$','fun_app$t'('nat$',A__questionmark_v0)) = 0 ) ) ) ).

%% fun_app$m(fun_app$n(?v1, ?v2), ?v3)
tff(formula_645,axiom,
    ! [A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( def_1(A__questionmark_v1,A__questionmark_v2,A__questionmark_v3) = tltrue )
    <=> 'fun_app$m'('fun_app$n'(A__questionmark_v1,A__questionmark_v2),A__questionmark_v3) ) ).

%% fun_app$(?v0, ?v2)
tff(formula_646,axiom,
    ! [A__questionmark_v0: 'A_run_bool_fun$',A__questionmark_v2: 'A_run$'] :
      ( ( def_2(A__questionmark_v0,A__questionmark_v2) = tltrue )
    <=> 'fun_app$'(A__questionmark_v0,A__questionmark_v2) ) ).

%% fun_app$(?v1, ?v2)
tff(formula_647,axiom,
    ! [A__questionmark_v1: 'A_run_bool_fun$',A__questionmark_v2: 'A_run$'] :
      ( ( def_3(A__questionmark_v1,A__questionmark_v2) = tltrue )
    <=> 'fun_app$'(A__questionmark_v1,A__questionmark_v2) ) ).

%% fun_app$o(case_prod$(?v1), ?v2)
tff(formula_648,axiom,
    ! [A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_prod$'] :
      ( ( def_4(A__questionmark_v1,A__questionmark_v2) = tltrue )
    <=> 'fun_app$o'('case_prod$'(A__questionmark_v1),A__questionmark_v2) ) ).

%% fun_app$m(fun_app$n(?v1, ?v3), ?v4)
tff(formula_649,axiom,
    ! [A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v4: 'Nat$',A__questionmark_v3: 'Nat$'] :
      ( ( def_5(A__questionmark_v1,A__questionmark_v4,A__questionmark_v3) = tltrue )
    <=> 'fun_app$m'('fun_app$n'(A__questionmark_v1,A__questionmark_v3),A__questionmark_v4) ) ).

%% fun_app$o(case_prod$(?v1), ?v2)
tff(formula_650,axiom,
    ! [A__questionmark_v1: 'Nat_nat_bool_fun_fun$',A__questionmark_v2: 'Nat_nat_prod$'] :
      ( ( def_6(A__questionmark_v1,A__questionmark_v2) = tltrue )
    <=> 'fun_app$o'('case_prod$'(A__questionmark_v1),A__questionmark_v2) ) ).

%% ∀ b:tlbool ((b = tltrue) ∨ (b = tlfalse))
tff(formula_651,axiom,
    ! [B: tlbool] :
      ( ( B = tltrue )
      | ( B = tlfalse ) ) ).

%% ¬(tltrue = tlfalse)
tff(formula_652,axiom,
    tltrue != tlfalse ).

%------------------------------------------------------------------------------

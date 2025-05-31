%------------------------------------------------------------------------------
% File     : SWW629_2 : TPTP v9.0.0. Released v6.1.0.
% Domain   : Software Verification
% Problem  : Mergesort queue-T-WP parameter mergesort
% Version  : Especial : Let and conditional terms encoded away.
% English  :

% Refs     : [Fil14] Filliatre (2014), Email to Geoff Sutcliffe
%          : [BF+]   Bobot et al. (URL), Toccata: Certified Programs and Cert
% Source   : [Fil14]
% Names    : mergesort_queue-T-WP_parameter_mergesort [Fil14]

% Status   : Theorem
% Rating   : 0.00 v8.2.0, 0.12 v7.5.0, 0.30 v7.4.0, 0.12 v7.3.0, 0.00 v7.0.0, 0.14 v6.4.0, 0.00 v6.3.0, 0.29 v6.2.0, 0.38 v6.1.0
% Syntax   : Number of formulae    :  114 (  41 unt;  40 typ;   0 def)
%            Number of atoms       :  159 (  60 equ)
%            Maximal formula atoms :   23 (   1 avg)
%            Number of connectives :   91 (   6   ~;   8   |;  22   &)
%                                         (   8 <=>;  47  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   24 (   5 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number arithmetic     :   29 (   6 atm;   8 fun;  12 num;   3 var)
%            Number of types       :    8 (   6 usr;   1 ari)
%            Number of type conns  :   51 (  25   >;  26   *;   0   +;   0  <<)
%            Number of predicates  :    8 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :   33 (  29 usr;  11 con; 0-5 aty)
%            Number of variables   :  212 ( 206   !;   6   ?; 212   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(uni,type,
    uni: $tType ).

tff(ty,type,
    ty: $tType ).

tff(sort,type,
    sort1: ( ty * uni ) > $o ).

tff(witness,type,
    witness1: ty > uni ).

tff(witness_sort1,axiom,
    ! [A: ty] : sort1(A,witness1(A)) ).

tff(int,type,
    int: ty ).

tff(real,type,
    real: ty ).

tff(bool,type,
    bool1: $tType ).

tff(bool1,type,
    bool: ty ).

tff(true,type,
    true1: bool1 ).

tff(false,type,
    false1: bool1 ).

tff(match_bool,type,
    match_bool1: ( ty * bool1 * uni * uni ) > uni ).

tff(match_bool_sort1,axiom,
    ! [A: ty,X: bool1,X1: uni,X2: uni] : sort1(A,match_bool1(A,X,X1,X2)) ).

tff(match_bool_True,axiom,
    ! [A: ty,Z: uni,Z1: uni] :
      ( sort1(A,Z)
     => ( match_bool1(A,true1,Z,Z1) = Z ) ) ).

tff(match_bool_False,axiom,
    ! [A: ty,Z: uni,Z1: uni] :
      ( sort1(A,Z1)
     => ( match_bool1(A,false1,Z,Z1) = Z1 ) ) ).

tff(true_False,axiom,
    true1 != false1 ).

tff(bool_inversion,axiom,
    ! [U: bool1] :
      ( ( U = true1 )
      | ( U = false1 ) ) ).

tff(tuple0,type,
    tuple02: $tType ).

tff(tuple01,type,
    tuple0: ty ).

tff(tuple02,type,
    tuple03: tuple02 ).

tff(tuple0_inversion,axiom,
    ! [U: tuple02] : ( U = tuple03 ) ).

tff(qtmark,type,
    qtmark: ty ).

tff(compatOrderMult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( $lesseq(X,Y)
     => ( $lesseq(0,Z)
       => $lesseq($product(X,Z),$product(Y,Z)) ) ) ).

tff(list,type,
    list: ty > ty ).

tff(nil,type,
    nil: ty > uni ).

tff(nil_sort1,axiom,
    ! [A: ty] : sort1(list(A),nil(A)) ).

tff(cons,type,
    cons: ( ty * uni * uni ) > uni ).

tff(cons_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(list(A),cons(A,X,X1)) ).

tff(match_list,type,
    match_list1: ( ty * ty * uni * uni * uni ) > uni ).

tff(match_list_sort1,axiom,
    ! [A: ty,A1: ty,X: uni,X1: uni,X2: uni] : sort1(A1,match_list1(A1,A,X,X1,X2)) ).

tff(match_list_Nil1,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni] :
      ( sort1(A1,Z)
     => ( match_list1(A1,A,nil(A),Z,Z1) = Z ) ) ).

tff(match_list_Cons1,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni,U: uni,U1: uni] :
      ( sort1(A1,Z1)
     => ( match_list1(A1,A,cons(A,U,U1),Z,Z1) = Z1 ) ) ).

tff(nil_Cons1,axiom,
    ! [A: ty,V: uni,V1: uni] : ( nil(A) != cons(A,V,V1) ) ).

tff(cons_proj_1,type,
    cons_proj_11: ( ty * uni ) > uni ).

tff(cons_proj_1_sort1,axiom,
    ! [A: ty,X: uni] : sort1(A,cons_proj_11(A,X)) ).

tff(cons_proj_1_def1,axiom,
    ! [A: ty,U: uni,U1: uni] :
      ( sort1(A,U)
     => ( cons_proj_11(A,cons(A,U,U1)) = U ) ) ).

tff(cons_proj_2,type,
    cons_proj_21: ( ty * uni ) > uni ).

tff(cons_proj_2_sort1,axiom,
    ! [A: ty,X: uni] : sort1(list(A),cons_proj_21(A,X)) ).

tff(cons_proj_2_def1,axiom,
    ! [A: ty,U: uni,U1: uni] : ( cons_proj_21(A,cons(A,U,U1)) = U1 ) ).

tff(list_inversion1,axiom,
    ! [A: ty,U: uni] :
      ( ( U = nil(A) )
      | ( U = cons(A,cons_proj_11(A,U),cons_proj_21(A,U)) ) ) ).

tff(mem,type,
    mem: ( ty * uni * uni ) > $o ).

tff(mem_def,axiom,
    ! [A: ty,X: uni] :
      ( sort1(A,X)
     => ( ~ mem(A,X,nil(A))
        & ! [X1: uni,X2: uni] :
            ( sort1(A,X1)
           => ( mem(A,X,cons(A,X1,X2))
            <=> ( ( X = X1 )
                | mem(A,X,X2) ) ) ) ) ) ).

tff(length,type,
    length2: ( ty * uni ) > $int ).

tff(length_def,axiom,
    ! [A: ty] :
      ( ( length2(A,nil(A)) = 0 )
      & ! [X: uni,X1: uni] : ( length2(A,cons(A,X,X1)) = $sum(1,length2(A,X1)) ) ) ).

tff(length_nonnegative,axiom,
    ! [A: ty,L: uni] : $lesseq(0,length2(A,L)) ).

tff(length_nil,axiom,
    ! [A: ty,L: uni] :
      ( ( length2(A,L) = 0 )
    <=> ( L = nil(A) ) ) ).

tff(infix_plpl,type,
    infix_plpl: ( ty * uni * uni ) > uni ).

tff(infix_plpl_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(list(A),infix_plpl(A,X,X1)) ).

tff(infix_plpl_def,axiom,
    ! [A: ty,L2: uni] :
      ( ( infix_plpl(A,nil(A),L2) = L2 )
      & ! [X: uni,X1: uni] : ( infix_plpl(A,cons(A,X,X1),L2) = cons(A,X,infix_plpl(A,X1,L2)) ) ) ).

tff(append_assoc,axiom,
    ! [A: ty,L1: uni,L2: uni,L3: uni] : ( infix_plpl(A,L1,infix_plpl(A,L2,L3)) = infix_plpl(A,infix_plpl(A,L1,L2),L3) ) ).

tff(append_l_nil,axiom,
    ! [A: ty,L: uni] : ( infix_plpl(A,L,nil(A)) = L ) ).

tff(append_length,axiom,
    ! [A: ty,L1: uni,L2: uni] : ( length2(A,infix_plpl(A,L1,L2)) = $sum(length2(A,L1),length2(A,L2)) ) ).

tff(mem_append,axiom,
    ! [A: ty,X: uni,L1: uni,L2: uni] :
      ( mem(A,X,infix_plpl(A,L1,L2))
    <=> ( mem(A,X,L1)
        | mem(A,X,L2) ) ) ).

tff(mem_decomp,axiom,
    ! [A: ty,X: uni,L: uni] :
      ( mem(A,X,L)
     => ? [L1: uni,L2: uni] :
          ( sort1(list(A),L1)
          & sort1(list(A),L2)
          & ( L = infix_plpl(A,L1,cons(A,X,L2)) ) ) ) ).

tff(num_occ,type,
    num_occ1: ( ty * uni * uni ) > $int ).

tff(num_occ_def,axiom,
    ! [A: ty,X: uni] :
      ( sort1(A,X)
     => ( ( num_occ1(A,X,nil(A)) = 0 )
        & ! [X1: uni,X2: uni] :
            ( sort1(A,X1)
           => ( ( ( X = X1 )
               => ( num_occ1(A,X,cons(A,X1,X2)) = $sum(1,num_occ1(A,X,X2)) ) )
              & ( ( X != X1 )
               => ( num_occ1(A,X,cons(A,X1,X2)) = $sum(0,num_occ1(A,X,X2)) ) ) ) ) ) ) ).

tff(mem_Num_Occ,axiom,
    ! [A: ty,X: uni,L: uni] :
      ( mem(A,X,L)
    <=> $less(0,num_occ1(A,X,L)) ) ).

tff(append_Num_Occ,axiom,
    ! [A: ty,X: uni,L1: uni,L2: uni] : ( num_occ1(A,X,infix_plpl(A,L1,L2)) = $sum(num_occ1(A,X,L1),num_occ1(A,X,L2)) ) ).

tff(reverse,type,
    reverse: ( ty * uni ) > uni ).

tff(reverse_sort1,axiom,
    ! [A: ty,X: uni] : sort1(list(A),reverse(A,X)) ).

tff(reverse_def,axiom,
    ! [A: ty] :
      ( ( reverse(A,nil(A)) = nil(A) )
      & ! [X: uni,X1: uni] : ( reverse(A,cons(A,X,X1)) = infix_plpl(A,reverse(A,X1),cons(A,X,nil(A))) ) ) ).

tff(reverse_append,axiom,
    ! [A: ty,L1: uni,L2: uni,X: uni] : ( infix_plpl(A,reverse(A,cons(A,X,L1)),L2) = infix_plpl(A,reverse(A,L1),cons(A,X,L2)) ) ).

tff(reverse_cons,axiom,
    ! [A: ty,L: uni,X: uni] : ( reverse(A,cons(A,X,L)) = infix_plpl(A,reverse(A,L),cons(A,X,nil(A))) ) ).

tff(reverse_reverse,axiom,
    ! [A: ty,L: uni] : ( reverse(A,reverse(A,L)) = L ) ).

tff(reverse_mem,axiom,
    ! [A: ty,L: uni,X: uni] :
      ( mem(A,X,L)
    <=> mem(A,X,reverse(A,L)) ) ).

tff(reverse_length,axiom,
    ! [A: ty,L: uni] : ( length2(A,reverse(A,L)) = length2(A,L) ) ).

tff(reverse_num_occ,axiom,
    ! [A: ty,X: uni,L: uni] : ( num_occ1(A,X,L) = num_occ1(A,X,reverse(A,L)) ) ).

tff(permut,type,
    permut: ( ty * uni * uni ) > $o ).

tff(permut_def,axiom,
    ! [A: ty,L1: uni,L2: uni] :
      ( ( permut(A,L1,L2)
       => ! [X: uni] : ( num_occ1(A,X,L1) = num_occ1(A,X,L2) ) )
      & ( ! [X: uni] :
            ( sort1(A,X)
           => ( num_occ1(A,X,L1) = num_occ1(A,X,L2) ) )
       => permut(A,L1,L2) ) ) ).

tff(permut_refl,axiom,
    ! [A: ty,L: uni] : permut(A,L,L) ).

tff(permut_sym,axiom,
    ! [A: ty,L1: uni,L2: uni] :
      ( permut(A,L1,L2)
     => permut(A,L2,L1) ) ).

tff(permut_trans,axiom,
    ! [A: ty,L1: uni,L2: uni,L3: uni] :
      ( permut(A,L1,L2)
     => ( permut(A,L2,L3)
       => permut(A,L1,L3) ) ) ).

tff(permut_cons,axiom,
    ! [A: ty,X: uni,L1: uni,L2: uni] :
      ( permut(A,L1,L2)
     => permut(A,cons(A,X,L1),cons(A,X,L2)) ) ).

tff(permut_swap,axiom,
    ! [A: ty,X: uni,Y: uni,L: uni] : permut(A,cons(A,X,cons(A,Y,L)),cons(A,Y,cons(A,X,L))) ).

tff(permut_cons_append,axiom,
    ! [A: ty,X: uni,L1: uni,L2: uni] : permut(A,infix_plpl(A,cons(A,X,L1),L2),infix_plpl(A,L1,cons(A,X,L2))) ).

tff(permut_assoc,axiom,
    ! [A: ty,L1: uni,L2: uni,L3: uni] : permut(A,infix_plpl(A,infix_plpl(A,L1,L2),L3),infix_plpl(A,L1,infix_plpl(A,L2,L3))) ).

tff(permut_append,axiom,
    ! [A: ty,L1: uni,L2: uni,K1: uni,K2: uni] :
      ( permut(A,L1,K1)
     => ( permut(A,L2,K2)
       => permut(A,infix_plpl(A,L1,L2),infix_plpl(A,K1,K2)) ) ) ).

tff(permut_append_swap,axiom,
    ! [A: ty,L1: uni,L2: uni] : permut(A,infix_plpl(A,L1,L2),infix_plpl(A,L2,L1)) ).

tff(permut_mem,axiom,
    ! [A: ty,X: uni,L1: uni,L2: uni] :
      ( permut(A,L1,L2)
     => ( mem(A,X,L1)
       => mem(A,X,L2) ) ) ).

tff(permut_length,axiom,
    ! [A: ty,L1: uni,L2: uni] :
      ( permut(A,L1,L2)
     => ( length2(A,L1) = length2(A,L2) ) ) ).

tff(t,type,
    t: ty > ty ).

tff(mk_t,type,
    mk_t: ( ty * uni ) > uni ).

tff(mk_t_sort1,axiom,
    ! [A: ty,X: uni] : sort1(t(A),mk_t(A,X)) ).

tff(elts,type,
    elts: ( ty * uni ) > uni ).

tff(elts_sort1,axiom,
    ! [A: ty,X: uni] : sort1(list(A),elts(A,X)) ).

tff(elts_def1,axiom,
    ! [A: ty,U: uni] : ( elts(A,mk_t(A,U)) = U ) ).

tff(t_inversion1,axiom,
    ! [A: ty,U: uni] : ( U = mk_t(A,elts(A,U)) ) ).

tff(length1,type,
    length3: ( ty * uni ) > $int ).

tff(length_def1,axiom,
    ! [A: ty,Q: uni] : ( length3(A,Q) = length2(A,elts(A,Q)) ) ).

tff(elt,type,
    elt1: $tType ).

tff(elt1,type,
    elt: ty ).

tff(le,type,
    le1: ( elt1 * elt1 ) > $o ).

tff(refl1,axiom,
    ! [X: elt1] : le1(X,X) ).

tff(trans1,axiom,
    ! [X: elt1,Y: elt1,Z: elt1] :
      ( le1(X,Y)
     => ( le1(Y,Z)
       => le1(X,Z) ) ) ).

tff(total1,axiom,
    ! [X: elt1,Y: elt1] :
      ( le1(X,Y)
      | le1(Y,X) ) ).

tff(list_elt,type,
    list_elt: $tType ).

tff(sorted,type,
    sorted1: list_elt > $o ).

tff(t2tb,type,
    t2tb: list_elt > uni ).

tff(t2tb_sort,axiom,
    ! [X: list_elt] : sort1(list(elt),t2tb(X)) ).

tff(tb2t,type,
    tb2t: uni > list_elt ).

tff(bridgeL,axiom,
    ! [I: list_elt] : ( tb2t(t2tb(I)) = I ) ).

tff(bridgeR,axiom,
    ! [J: uni] : ( t2tb(tb2t(J)) = J ) ).

tff(sorted_Nil,axiom,
    sorted1(tb2t(nil(elt))) ).

tff(t2tb1,type,
    t2tb1: elt1 > uni ).

tff(t2tb_sort1,axiom,
    ! [X: elt1] : sort1(elt,t2tb1(X)) ).

tff(tb2t1,type,
    tb2t1: uni > elt1 ).

tff(bridgeL1,axiom,
    ! [I: elt1] : ( tb2t1(t2tb1(I)) = I ) ).

tff(bridgeR1,axiom,
    ! [J: uni] :
      ( sort1(elt,J)
     => ( t2tb1(tb2t1(J)) = J ) ) ).

tff(sorted_One,axiom,
    ! [X: elt1] : sorted1(tb2t(cons(elt,t2tb1(X),nil(elt)))) ).

tff(sorted_Two,axiom,
    ! [X: elt1,Y: elt1,L: list_elt] :
      ( le1(X,Y)
     => ( sorted1(tb2t(cons(elt,t2tb1(Y),t2tb(L))))
       => sorted1(tb2t(cons(elt,t2tb1(X),cons(elt,t2tb1(Y),t2tb(L))))) ) ) ).

tff(sorted_inversion,axiom,
    ! [Z: list_elt] :
      ( sorted1(Z)
     => ( ( Z = tb2t(nil(elt)) )
        | ? [X: elt1] : ( Z = tb2t(cons(elt,t2tb1(X),nil(elt))) )
        | ? [X: elt1,Y: elt1,L: list_elt] :
            ( le1(X,Y)
            & sorted1(tb2t(cons(elt,t2tb1(Y),t2tb(L))))
            & ( Z = tb2t(cons(elt,t2tb1(X),cons(elt,t2tb1(Y),t2tb(L)))) ) ) ) ) ).

tff(sorted_mem,axiom,
    ! [X: elt1,L: list_elt] :
      ( ( ! [Y: elt1] :
            ( mem(elt,t2tb1(Y),t2tb(L))
           => le1(X,Y) )
        & sorted1(L) )
    <=> sorted1(tb2t(cons(elt,t2tb1(X),t2tb(L)))) ) ).

tff(sorted_append,axiom,
    ! [L1: list_elt,L2: list_elt] :
      ( ( sorted1(L1)
        & sorted1(L2)
        & ! [X: elt1,Y: elt1] :
            ( mem(elt,t2tb1(X),t2tb(L1))
           => ( mem(elt,t2tb1(Y),t2tb(L2))
             => le1(X,Y) ) ) )
    <=> sorted1(tb2t(infix_plpl(elt,t2tb(L1),t2tb(L2)))) ) ).

tff(wP_parameter_mergesort,conjecture,
    ! [Q: list_elt] :
      ( $less(1,length2(elt,t2tb(Q)))
     => ! [Q1: list_elt] :
          ( ( Q1 = tb2t(nil(elt)) )
         => ! [Q2: list_elt] :
              ( ( Q2 = tb2t(nil(elt)) )
             => ! [Q21: list_elt,Q11: list_elt,Q3: list_elt] :
                  ( ( permut(elt,infix_plpl(elt,infix_plpl(elt,t2tb(Q11),t2tb(Q21)),t2tb(Q3)),t2tb(Q))
                    & ( ( length2(elt,t2tb(Q11)) = length2(elt,t2tb(Q21)) )
                      | ( ( length2(elt,t2tb(Q3)) = 0 )
                        & ( length2(elt,t2tb(Q11)) = $sum(length2(elt,t2tb(Q21)),1) ) ) ) )
                 => ! [O: bool1] :
                      ( ( ( O = true1 )
                      <=> ( Q3 = tb2t(nil(elt)) ) )
                     => ( ~ ( ( O != true1 ) )
                       => ( ( Q3 = tb2t(nil(elt)) )
                         => ( permut(elt,infix_plpl(elt,t2tb(Q11),t2tb(Q21)),t2tb(Q))
                           => ! [Q12: list_elt] :
                                ( ( sorted1(Q12)
                                  & permut(elt,t2tb(Q12),t2tb(Q11)) )
                               => ! [Q22: list_elt] :
                                    ( ( sorted1(Q22)
                                      & permut(elt,t2tb(Q22),t2tb(Q21)) )
                                   => ( ( ( Q3 = tb2t(nil(elt)) )
                                        & sorted1(Q12)
                                        & sorted1(Q22) )
                                     => ! [Q4: list_elt] :
                                          ( ( sorted1(Q4)
                                            & permut(elt,t2tb(Q4),infix_plpl(elt,t2tb(Q12),t2tb(Q22))) )
                                         => ( sorted1(Q4)
                                            & permut(elt,t2tb(Q4),t2tb(Q)) ) ) ) ) ) ) ) ) ) ) ) ) ) ).

%------------------------------------------------------------------------------

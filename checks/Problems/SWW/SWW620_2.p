%------------------------------------------------------------------------------
% File     : SWW620_2 : TPTP v9.0.0. Released v6.1.0.
% Domain   : Software Verification
% Problem  : Mergesort array-T-WP parameter find run
% Version  : Especial : Let and conditional terms encoded away.
% English  :

% Refs     : [Fil14] Filliatre (2014), Email to Geoff Sutcliffe
%          : [BF+]   Bobot et al. (URL), Toccata: Certified Programs and Cert
% Source   : [Fil14]
% Names    : mergesort_array-T-WP_parameter_find_run [Fil14]

% Status   : Theorem
% Rating   : 0.12 v8.2.0, 0.38 v7.5.0, 0.40 v7.4.0, 0.12 v7.3.0, 0.00 v7.0.0, 0.14 v6.4.0, 0.00 v6.3.0, 0.43 v6.2.0, 0.50 v6.1.0
% Syntax   : Number of formulae    :  157 (  33 unt;  59 typ;   0 def)
%            Number of atoms       :  254 (  76 equ)
%            Maximal formula atoms :   12 (   1 avg)
%            Number of connectives :  168 (  12   ~;   4   |;  63   &)
%                                         (  11 <=>;  78  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   20 (   6 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number arithmetic     :  321 ( 107 atm;  21 fun;  58 num; 135 var)
%            Number of types       :    9 (   7 usr;   1 ari)
%            Number of type conns  :  115 (  43   >;  72   *;   0   +;   0  <<)
%            Number of predicates  :   16 (  13 usr;   0 prp; 1-7 aty)
%            Number of functors    :   45 (  39 usr;  11 con; 0-5 aty)
%            Number of variables   :  301 ( 299   !;   2   ?; 301   :)
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

tff(match_bool_sort4,axiom,
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

tff(map,type,
    map: ( ty * ty ) > ty ).

tff(get,type,
    get: ( ty * ty * uni * uni ) > uni ).

tff(get_sort8,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni] : sort1(B,get(B,A,X,X1)) ).

tff(set,type,
    set: ( ty * ty * uni * uni * uni ) > uni ).

tff(set_sort8,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni,X2: uni] : sort1(map(A,B),set(B,A,X,X1,X2)) ).

tff(select_eq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni,B1: uni] :
      ( sort1(B,B1)
     => ( ( A1 = A2 )
       => ( get(B,A,set(B,A,M,A1,B1),A2) = B1 ) ) ) ).

tff(select_neq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni] :
      ( sort1(A,A1)
     => ( sort1(A,A2)
       => ! [B1: uni] :
            ( ( A1 != A2 )
           => ( get(B,A,set(B,A,M,A1,B1),A2) = get(B,A,M,A2) ) ) ) ) ).

tff(const1,type,
    const: ( ty * ty * uni ) > uni ).

tff(const_sort4,axiom,
    ! [A: ty,B: ty,X: uni] : sort1(map(A,B),const(B,A,X)) ).

tff(const,axiom,
    ! [A: ty,B: ty,B1: uni,A1: uni] :
      ( sort1(B,B1)
     => ( get(B,A,const(B,A,B1),A1) = B1 ) ) ).

tff(array,type,
    array: ty > ty ).

tff(mk_array,type,
    mk_array1: ( ty * $int * uni ) > uni ).

tff(mk_array_sort4,axiom,
    ! [A: ty,X: $int,X1: uni] : sort1(array(A),mk_array1(A,X,X1)) ).

tff(length,type,
    length1: ( ty * uni ) > $int ).

tff(length_def1,axiom,
    ! [A: ty,U: $int,U1: uni] : ( length1(A,mk_array1(A,U,U1)) = U ) ).

tff(elts,type,
    elts: ( ty * uni ) > uni ).

tff(elts_sort4,axiom,
    ! [A: ty,X: uni] : sort1(map(int,A),elts(A,X)) ).

tff(elts_def1,axiom,
    ! [A: ty,U: $int,U1: uni] :
      ( sort1(map(int,A),U1)
     => ( elts(A,mk_array1(A,U,U1)) = U1 ) ) ).

tff(array_inversion1,axiom,
    ! [A: ty,U: uni] : ( U = mk_array1(A,length1(A,U),elts(A,U)) ) ).

tff(get1,type,
    get2: ( ty * uni * $int ) > uni ).

tff(get_sort9,axiom,
    ! [A: ty,X: uni,X1: $int] : sort1(A,get2(A,X,X1)) ).

tff(t2tb,type,
    t2tb: $int > uni ).

tff(t2tb_sort12,axiom,
    ! [X: $int] : sort1(int,t2tb(X)) ).

tff(tb2t,type,
    tb2t: uni > $int ).

tff(bridgeL,axiom,
    ! [I: $int] : ( tb2t(t2tb(I)) = I ) ).

tff(bridgeR,axiom,
    ! [J: uni] : ( t2tb(tb2t(J)) = J ) ).

tff(get_def,axiom,
    ! [A: ty,A1: uni,I: $int] : ( get2(A,A1,I) = get(A,int,elts(A,A1),t2tb(I)) ) ).

tff(set1,type,
    set2: ( ty * uni * $int * uni ) > uni ).

tff(set_sort9,axiom,
    ! [A: ty,X: uni,X1: $int,X2: uni] : sort1(array(A),set2(A,X,X1,X2)) ).

tff(set_def,axiom,
    ! [A: ty,A1: uni,I: $int,V: uni] : ( set2(A,A1,I,V) = mk_array1(A,length1(A,A1),set(A,int,elts(A,A1),t2tb(I),V)) ) ).

tff(make,type,
    make1: ( ty * $int * uni ) > uni ).

tff(make_sort4,axiom,
    ! [A: ty,X: $int,X1: uni] : sort1(array(A),make1(A,X,X1)) ).

tff(make_def,axiom,
    ! [A: ty,N: $int,V: uni] : ( make1(A,N,V) = mk_array1(A,N,const(A,int,V)) ) ).

tff(elt6,type,
    elt6: $tType ).

tff(elt7,type,
    elt7: ty ).

tff(le3,type,
    le4: ( elt6 * elt6 ) > $o ).

tff(refl4,axiom,
    ! [X: elt6] : le4(X,X) ).

tff(trans4,axiom,
    ! [X: elt6,Y: elt6,Z: elt6] :
      ( le4(X,Y)
     => ( le4(Y,Z)
       => le4(X,Z) ) ) ).

tff(total4,axiom,
    ! [X: elt6,Y: elt6] :
      ( le4(X,Y)
      | le4(Y,X) ) ).

tff(array_elt3,type,
    array_elt3: $tType ).

tff(sorted_sub3,type,
    sorted_sub4: ( array_elt3 * $int * $int ) > $o ).

tff(t2tb10,type,
    t2tb10: array_elt3 > uni ).

tff(t2tb_sort13,axiom,
    ! [X: array_elt3] : sort1(array(elt7),t2tb10(X)) ).

tff(tb2t10,type,
    tb2t10: uni > array_elt3 ).

tff(bridgeL10,axiom,
    ! [I: array_elt3] : ( tb2t10(t2tb10(I)) = I ) ).

tff(bridgeR10,axiom,
    ! [J: uni] : ( t2tb10(tb2t10(J)) = J ) ).

tff(t2tb11,type,
    t2tb11: elt6 > uni ).

tff(t2tb_sort14,axiom,
    ! [X: elt6] : sort1(elt7,t2tb11(X)) ).

tff(tb2t11,type,
    tb2t11: uni > elt6 ).

tff(bridgeL11,axiom,
    ! [I: elt6] : ( tb2t11(t2tb11(I)) = I ) ).

tff(bridgeR11,axiom,
    ! [J: uni] :
      ( sort1(elt7,J)
     => ( t2tb11(tb2t11(J)) = J ) ) ).

tff(sorted_sub_def3,axiom,
    ! [A: array_elt3,L: $int,U: $int] :
      ( sorted_sub4(A,L,U)
    <=> ! [I1: $int,I2: $int] :
          ( ( $lesseq(L,I1)
            & $lesseq(I1,I2)
            & $less(I2,U) )
         => le4(tb2t11(get2(elt7,t2tb10(A),I1)),tb2t11(get2(elt7,t2tb10(A),I2))) ) ) ).

tff(sorted3,type,
    sorted4: array_elt3 > $o ).

tff(sorted_def3,axiom,
    ! [A: array_elt3] :
      ( sorted4(A)
    <=> ! [I1: $int,I2: $int] :
          ( ( $lesseq(0,I1)
            & $lesseq(I1,I2)
            & $less(I2,length1(elt7,t2tb10(A))) )
         => le4(tb2t11(get2(elt7,t2tb10(A),I1)),tb2t11(get2(elt7,t2tb10(A),I2))) ) ) ).

tff(ref,type,
    ref: ty > ty ).

tff(mk_ref,type,
    mk_ref: ( ty * uni ) > uni ).

tff(mk_ref_sort4,axiom,
    ! [A: ty,X: uni] : sort1(ref(A),mk_ref(A,X)) ).

tff(contents,type,
    contents: ( ty * uni ) > uni ).

tff(contents_sort4,axiom,
    ! [A: ty,X: uni] : sort1(A,contents(A,X)) ).

tff(contents_def4,axiom,
    ! [A: ty,U: uni] :
      ( sort1(A,U)
     => ( contents(A,mk_ref(A,U)) = U ) ) ).

tff(ref_inversion4,axiom,
    ! [A: ty,U: uni] :
      ( sort1(ref(A),U)
     => ( U = mk_ref(A,contents(A,U)) ) ) ).

tff(occ,type,
    occ1: ( ty * uni * uni * $int * $int ) > $int ).

tff(occ_empty,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( $lesseq(U,L)
     => ( occ1(A,V,M,L,U) = 0 ) ) ).

tff(occ_right_no_add,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( sort1(A,V)
     => ( $less(L,U)
       => ( ( get(A,int,M,t2tb($difference(U,1))) != V )
         => ( occ1(A,V,M,L,U) = occ1(A,V,M,L,$difference(U,1)) ) ) ) ) ).

tff(occ_right_add,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( $less(L,U)
     => ( ( get(A,int,M,t2tb($difference(U,1))) = V )
       => ( occ1(A,V,M,L,U) = $sum(1,occ1(A,V,M,L,$difference(U,1))) ) ) ) ).

tff(occ_bounds,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( $lesseq(L,U)
     => ( $lesseq(0,occ1(A,V,M,L,U))
        & $lesseq(occ1(A,V,M,L,U),$difference(U,L)) ) ) ).

tff(occ_append,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,Mid: $int,U: $int] :
      ( ( $lesseq(L,Mid)
        & $lesseq(Mid,U) )
     => ( occ1(A,V,M,L,U) = $sum(occ1(A,V,M,L,Mid),occ1(A,V,M,Mid,U)) ) ) ).

tff(occ_neq,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( sort1(A,V)
     => ( ! [I: $int] :
            ( ( $lesseq(L,I)
              & $less(I,U) )
           => ( get(A,int,M,t2tb(I)) != V ) )
       => ( occ1(A,V,M,L,U) = 0 ) ) ) ).

tff(occ_exists,axiom,
    ! [A: ty,V: uni,M: uni,L: $int,U: $int] :
      ( sort1(A,V)
     => ( $less(0,occ1(A,V,M,L,U))
       => ? [I: $int] :
            ( $lesseq(L,I)
            & $less(I,U)
            & ( get(A,int,M,t2tb(I)) = V ) ) ) ) ).

tff(occ_pos,axiom,
    ! [A: ty,M: uni,L: $int,U: $int,I: $int] :
      ( ( $lesseq(L,I)
        & $less(I,U) )
     => $less(0,occ1(A,get(A,int,M,t2tb(I)),M,L,U)) ) ).

tff(occ_eq,axiom,
    ! [A: ty,V: uni,M1: uni,M2: uni,L: $int,U: $int] :
      ( ! [I: $int] :
          ( ( $lesseq(L,I)
            & $less(I,U) )
         => ( get(A,int,M1,t2tb(I)) = get(A,int,M2,t2tb(I)) ) )
     => ( occ1(A,V,M1,L,U) = occ1(A,V,M2,L,U) ) ) ).

tff(permut,type,
    permut2: ( ty * uni * uni * $int * $int ) > $o ).

tff(permut_def,axiom,
    ! [A: ty,M1: uni,M2: uni,L: $int,U: $int] :
      ( ( permut2(A,M1,M2,L,U)
       => ! [V: uni] : ( occ1(A,V,M1,L,U) = occ1(A,V,M2,L,U) ) )
      & ( ! [V: uni] :
            ( sort1(A,V)
           => ( occ1(A,V,M1,L,U) = occ1(A,V,M2,L,U) ) )
       => permut2(A,M1,M2,L,U) ) ) ).

tff(permut_trans,axiom,
    ! [A: ty,A1: uni,A2: uni,A3: uni,L: $int,U: $int] :
      ( permut2(A,A1,A2,L,U)
     => ( permut2(A,A2,A3,L,U)
       => permut2(A,A1,A3,L,U) ) ) ).

tff(permut_exists,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int,I: $int] :
      ( permut2(A,A1,A2,L,U)
     => ( ( $lesseq(L,I)
          & $less(I,U) )
       => ? [J: $int] :
            ( $lesseq(L,J)
            & $less(J,U)
            & ( get(A,int,A1,t2tb(J)) = get(A,int,A2,t2tb(I)) ) ) ) ) ).

tff(map_eq_sub,type,
    map_eq_sub1: ( ty * uni * uni * $int * $int ) > $o ).

tff(map_eq_sub_def,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int] :
      ( map_eq_sub1(A,A1,A2,L,U)
    <=> ! [I: $int] :
          ( ( $lesseq(L,I)
            & $less(I,U) )
         => ( get(A,int,A1,t2tb(I)) = get(A,int,A2,t2tb(I)) ) ) ) ).

tff(array_eq_sub,type,
    array_eq_sub1: ( ty * uni * uni * $int * $int ) > $o ).

tff(array_eq_sub_def,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int] :
      ( array_eq_sub1(A,A1,A2,L,U)
    <=> ( ( length1(A,A1) = length1(A,A2) )
        & $lesseq(0,L)
        & $lesseq(L,length1(A,A1))
        & $lesseq(0,U)
        & $lesseq(U,length1(A,A1))
        & map_eq_sub1(A,elts(A,A1),elts(A,A2),L,U) ) ) ).

tff(array_eq,type,
    array_eq: ( ty * uni * uni ) > $o ).

tff(array_eq_def,axiom,
    ! [A: ty,A1: uni,A2: uni] :
      ( array_eq(A,A1,A2)
    <=> ( ( length1(A,A1) = length1(A,A2) )
        & map_eq_sub1(A,elts(A,A1),elts(A,A2),0,length1(A,A1)) ) ) ).

tff(exchange,type,
    exchange2: ( ty * uni * uni * $int * $int * $int * $int ) > $o ).

tff(exchange_def,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int,I: $int,J: $int] :
      ( exchange2(A,A1,A2,L,U,I,J)
    <=> ( $lesseq(L,I)
        & $less(I,U)
        & $lesseq(L,J)
        & $less(J,U)
        & ( get(A,int,A1,t2tb(I)) = get(A,int,A2,t2tb(J)) )
        & ( get(A,int,A1,t2tb(J)) = get(A,int,A2,t2tb(I)) )
        & ! [K: $int] :
            ( ( $lesseq(L,K)
              & $less(K,U) )
           => ( ( K != I )
             => ( ( K != J )
               => ( get(A,int,A1,t2tb(K)) = get(A,int,A2,t2tb(K)) ) ) ) ) ) ) ).

tff(exchange_set,axiom,
    ! [A: ty,A1: uni,L: $int,U: $int,I: $int,J: $int] :
      ( ( $lesseq(L,I)
        & $less(I,U) )
     => ( ( $lesseq(L,J)
          & $less(J,U) )
       => exchange2(A,A1,set(A,int,set(A,int,A1,t2tb(I),get(A,int,A1,t2tb(J))),t2tb(J),get(A,int,A1,t2tb(I))),L,U,I,J) ) ) ).

tff(exchange1,type,
    exchange3: ( ty * uni * uni * $int * $int ) > $o ).

tff(exchange_def1,axiom,
    ! [A: ty,A1: uni,A2: uni,I: $int,J: $int] :
      ( exchange3(A,A1,A2,I,J)
    <=> ( ( length1(A,A1) = length1(A,A2) )
        & exchange2(A,elts(A,A1),elts(A,A2),0,length1(A,A1),I,J) ) ) ).

tff(permut1,type,
    permut3: ( ty * uni * uni * $int * $int ) > $o ).

tff(permut_def1,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int] :
      ( permut3(A,A1,A2,L,U)
    <=> ( ( length1(A,A1) = length1(A,A2) )
        & $lesseq(0,L)
        & $lesseq(L,length1(A,A1))
        & $lesseq(0,U)
        & $lesseq(U,length1(A,A1))
        & permut2(A,elts(A,A1),elts(A,A2),L,U) ) ) ).

tff(permut_sub,type,
    permut_sub1: ( ty * uni * uni * $int * $int ) > $o ).

tff(permut_sub_def,axiom,
    ! [A: ty,A1: uni,A2: uni,L: $int,U: $int] :
      ( permut_sub1(A,A1,A2,L,U)
    <=> ( map_eq_sub1(A,elts(A,A1),elts(A,A2),0,L)
        & permut3(A,A1,A2,L,U)
        & map_eq_sub1(A,elts(A,A1),elts(A,A2),U,length1(A,A1)) ) ) ).

tff(permut_all,type,
    permut_all: ( ty * uni * uni ) > $o ).

tff(permut_all_def,axiom,
    ! [A: ty,A1: uni,A2: uni] :
      ( permut_all(A,A1,A2)
    <=> ( ( length1(A,A1) = length1(A,A2) )
        & permut2(A,elts(A,A1),elts(A,A2),0,length1(A,A1)) ) ) ).

tff(exchange_permut_sub,axiom,
    ! [A: ty,A1: uni,A2: uni,I: $int,J: $int,L: $int,U: $int] :
      ( exchange3(A,A1,A2,I,J)
     => ( ( $lesseq(L,I)
          & $less(I,U) )
       => ( ( $lesseq(L,J)
            & $less(J,U) )
         => ( $lesseq(0,L)
           => ( $lesseq(U,length1(A,A1))
             => permut_sub1(A,A1,A2,L,U) ) ) ) ) ) ).

tff(permut_sub_weakening,axiom,
    ! [A: ty,A1: uni,A2: uni,L1: $int,U1: $int,L2: $int,U2: $int] :
      ( permut_sub1(A,A1,A2,L1,U1)
     => ( ( $lesseq(0,L2)
          & $lesseq(L2,L1) )
       => ( ( $lesseq(U1,U2)
            & $lesseq(U2,length1(A,A1)) )
         => permut_sub1(A,A1,A2,L2,U2) ) ) ) ).

tff(exchange_permut_all,axiom,
    ! [A: ty,A1: uni,A2: uni,I: $int,J: $int] :
      ( exchange3(A,A1,A2,I,J)
     => permut_all(A,A1,A2) ) ).

tff(abs,type,
    abs: $int > $int ).

tff(abs_def,axiom,
    ! [X: $int] :
      ( ( $lesseq(0,X)
       => ( abs(X) = X ) )
      & ( ~ $lesseq(0,X)
       => ( abs(X) = $uminus(X) ) ) ) ).

tff(abs_le,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(abs(X),Y)
    <=> ( $lesseq($uminus(Y),X)
        & $lesseq(X,Y) ) ) ).

tff(abs_pos,axiom,
    ! [X: $int] : $lesseq(0,abs(X)) ).

tff(div,type,
    div: ( $int * $int ) > $int ).

tff(mod,type,
    mod: ( $int * $int ) > $int ).

tff(div_mod,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => ( X = $sum($product(Y,div(X,Y)),mod(X,Y)) ) ) ).

tff(div_bound,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(0,Y) )
     => ( $lesseq(0,div(X,Y))
        & $lesseq(div(X,Y),X) ) ) ).

tff(mod_bound,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => ( $less($uminus(abs(Y)),mod(X,Y))
        & $less(mod(X,Y),abs(Y)) ) ) ).

tff(div_sign_pos,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(0,Y) )
     => $lesseq(0,div(X,Y)) ) ).

tff(div_sign_neg,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
        & $less(0,Y) )
     => $lesseq(div(X,Y),0) ) ).

tff(mod_sign_pos,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & ( Y != 0 ) )
     => $lesseq(0,mod(X,Y)) ) ).

tff(mod_sign_neg,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
        & ( Y != 0 ) )
     => $lesseq(mod(X,Y),0) ) ).

tff(rounds_toward_zero,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => $lesseq(abs($product(div(X,Y),Y)),abs(X)) ) ).

tff(div_1,axiom,
    ! [X: $int] : ( div(X,1) = X ) ).

tff(mod_1,axiom,
    ! [X: $int] : ( mod(X,1) = 0 ) ).

tff(div_inf,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(X,Y) )
     => ( div(X,Y) = 0 ) ) ).

tff(mod_inf,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(X,Y) )
     => ( mod(X,Y) = X ) ) ).

tff(div_mult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( ( $less(0,X)
        & $lesseq(0,Y)
        & $lesseq(0,Z) )
     => ( div($sum($product(X,Y),Z),X) = $sum(Y,div(Z,X)) ) ) ).

tff(mod_mult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( ( $less(0,X)
        & $lesseq(0,Y)
        & $lesseq(0,Z) )
     => ( mod($sum($product(X,Y),Z),X) = mod(Z,X) ) ) ).

tff(min,type,
    min: ( $int * $int ) > $int ).

tff(max,type,
    max: ( $int * $int ) > $int ).

tff(max_is_ge,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(X,max(X,Y))
      & $lesseq(Y,max(X,Y)) ) ).

tff(max_is_some,axiom,
    ! [X: $int,Y: $int] :
      ( ( max(X,Y) = X )
      | ( max(X,Y) = Y ) ) ).

tff(min_is_le,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(min(X,Y),X)
      & $lesseq(min(X,Y),Y) ) ).

tff(min_is_some,axiom,
    ! [X: $int,Y: $int] :
      ( ( min(X,Y) = X )
      | ( min(X,Y) = Y ) ) ).

tff(max_x,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(Y,X)
     => ( max(X,Y) = X ) ) ).

tff(max_y,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(X,Y)
     => ( max(X,Y) = Y ) ) ).

tff(min_x,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(X,Y)
     => ( min(X,Y) = X ) ) ).

tff(min_y,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(Y,X)
     => ( min(X,Y) = Y ) ) ).

tff(max_sym,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(Y,X)
     => ( max(X,Y) = max(Y,X) ) ) ).

tff(min_sym,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(Y,X)
     => ( min(X,Y) = min(Y,X) ) ) ).

tff(map_int_elt3,type,
    map_int_elt3: $tType ).

tff(t2tb12,type,
    t2tb12: map_int_elt3 > uni ).

tff(t2tb_sort15,axiom,
    ! [X: map_int_elt3] : sort1(map(int,elt7),t2tb12(X)) ).

tff(tb2t12,type,
    tb2t12: uni > map_int_elt3 ).

tff(bridgeL12,axiom,
    ! [I: map_int_elt3] : ( tb2t12(t2tb12(I)) = I ) ).

tff(bridgeR12,axiom,
    ! [J: uni] :
      ( sort1(map(int,elt7),J)
     => ( t2tb12(tb2t12(J)) = J ) ) ).

tff(wP_parameter_find_run,conjecture,
    ! [A: $int,A1: map_int_elt3,Lo: $int] :
      ( ( $lesseq(0,A)
        & $lesseq(0,Lo)
        & $less(Lo,A) )
     => sorted_sub4(tb2t10(mk_array1(elt7,A,t2tb12(A1))),Lo,$sum(Lo,1)) ) ).

%------------------------------------------------------------------------------

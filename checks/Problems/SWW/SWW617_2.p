%------------------------------------------------------------------------------
% File     : SWW617_2 : TPTP v9.0.0. Released v6.1.0.
% Domain   : Software Verification
% Problem  : Max matrix-T-WP parameter maximum
% Version  : Especial : Let and conditional terms encoded away.
% English  :

% Refs     : [Fil14] Filliatre (2014), Email to Geoff Sutcliffe
%          : [BF+]   Bobot et al. (URL), Toccata: Certified Programs and Cert
% Source   : [Fil14]
% Names    : max_matrix-T-WP_parameter_maximum [Fil14]

% Status   : Theorem
% Rating   : 0.75 v9.0.0, 0.62 v8.2.0, 0.88 v7.5.0, 0.90 v7.4.0, 0.88 v7.3.0, 0.83 v7.0.0, 0.71 v6.4.0, 1.00 v6.3.0, 0.86 v6.2.0, 1.00 v6.1.0
% Syntax   : Number of formulae    :  173 (  50 unt;  77 typ;   0 def)
%            Number of atoms       :  187 (  71 equ)
%            Maximal formula atoms :   12 (   1 avg)
%            Number of connectives :   98 (   7   ~;   4   |;  28   &)
%                                         (   7 <=>;  52  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   16 (   4 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number arithmetic     :  149 (  53 atm;  12 fun;  24 num;  60 var)
%            Number of types       :   14 (  12 usr;   1 ari)
%            Number of type conns  :  100 (  53   >;  47   *;   0   +;   0  <<)
%            Number of predicates  :    9 (   6 usr;   0 prp; 1-2 aty)
%            Number of functors    :   64 (  59 usr;  14 con; 0-5 aty)
%            Number of variables   :  221 ( 221   !;   0   ?; 221   :)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(uni,type,
    uni: $tType ).

tff(ty,type,
    ty: $tType ).

tff(sort,type,
    sort: ( ty * uni ) > $o ).

tff(witness,type,
    witness: ty > uni ).

tff(witness_sort,axiom,
    ! [A: ty] : sort(A,witness(A)) ).

tff(int,type,
    int: ty ).

tff(real,type,
    real: ty ).

tff(bool,type,
    bool: $tType ).

tff(bool1,type,
    bool1: ty ).

tff(true,type,
    true: bool ).

tff(false,type,
    false: bool ).

tff(match_bool,type,
    match_bool: ( ty * bool * uni * uni ) > uni ).

tff(match_bool_sort,axiom,
    ! [A: ty,X: bool,X1: uni,X2: uni] : sort(A,match_bool(A,X,X1,X2)) ).

tff(match_bool_True,axiom,
    ! [A: ty,Z: uni,Z1: uni] :
      ( sort(A,Z)
     => ( match_bool(A,true,Z,Z1) = Z ) ) ).

tff(match_bool_False,axiom,
    ! [A: ty,Z: uni,Z1: uni] :
      ( sort(A,Z1)
     => ( match_bool(A,false,Z,Z1) = Z1 ) ) ).

tff(true_False,axiom,
    true != false ).

tff(bool_inversion,axiom,
    ! [U: bool] :
      ( ( U = true )
      | ( U = false ) ) ).

tff(tuple0,type,
    tuple0: $tType ).

tff(tuple01,type,
    tuple01: ty ).

tff(tuple02,type,
    tuple02: tuple0 ).

tff(tuple0_inversion,axiom,
    ! [U: tuple0] : ( U = tuple02 ) ).

tff(qtmark,type,
    qtmark: ty ).

tff(compatOrderMult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( $lesseq(X,Y)
     => ( $lesseq(0,Z)
       => $lesseq($product(X,Z),$product(Y,Z)) ) ) ).

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

tff(map,type,
    map: ( ty * ty ) > ty ).

tff(get,type,
    get: ( ty * ty * uni * uni ) > uni ).

tff(get_sort,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni] : sort(B,get(B,A,X,X1)) ).

tff(set,type,
    set: ( ty * ty * uni * uni * uni ) > uni ).

tff(set_sort,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni,X2: uni] : sort(map(A,B),set(B,A,X,X1,X2)) ).

tff(select_eq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni,B1: uni] :
      ( sort(B,B1)
     => ( ( A1 = A2 )
       => ( get(B,A,set(B,A,M,A1,B1),A2) = B1 ) ) ) ).

tff(select_neq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni] :
      ( sort(A,A1)
     => ( sort(A,A2)
       => ! [B1: uni] :
            ( ( A1 != A2 )
           => ( get(B,A,set(B,A,M,A1,B1),A2) = get(B,A,M,A2) ) ) ) ) ).

tff(const,type,
    const: ( ty * ty * uni ) > uni ).

tff(const_sort,axiom,
    ! [A: ty,B: ty,X: uni] : sort(map(A,B),const(B,A,X)) ).

tff(const1,axiom,
    ! [A: ty,B: ty,B1: uni,A1: uni] :
      ( sort(B,B1)
     => ( get(B,A,const(B,A,B1),A1) = B1 ) ) ).

tff(ref,type,
    ref: ty > ty ).

tff(mk_ref,type,
    mk_ref: ( ty * uni ) > uni ).

tff(mk_ref_sort,axiom,
    ! [A: ty,X: uni] : sort(ref(A),mk_ref(A,X)) ).

tff(contents,type,
    contents: ( ty * uni ) > uni ).

tff(contents_sort,axiom,
    ! [A: ty,X: uni] : sort(A,contents(A,X)) ).

tff(contents_def,axiom,
    ! [A: ty,U: uni] :
      ( sort(A,U)
     => ( contents(A,mk_ref(A,U)) = U ) ) ).

tff(ref_inversion,axiom,
    ! [A: ty,U: uni] :
      ( sort(ref(A),U)
     => ( U = mk_ref(A,contents(A,U)) ) ) ).

tff(n,type,
    n: $int ).

tff(n_nonneg,axiom,
    $lesseq(0,n) ).

tff(size,type,
    size: $int ).

tff(set1,type,
    set1: $tType ).

tff(set2,type,
    set2: ty ).

tff(mem,type,
    mem: ( $int * set1 ) > $o ).

tff(remove,type,
    remove: ( $int * set1 ) > set1 ).

tff(remove_def1,axiom,
    ! [X: $int,Y: $int,S: set1] :
      ( mem(X,remove(Y,S))
    <=> ( ( X != Y )
        & mem(X,S) ) ) ).

tff(below,type,
    below: $int > set1 ).

tff(below_def,axiom,
    ! [X: $int,N: $int] :
      ( ( $lesseq(0,N)
        & $lesseq(N,size) )
     => ( mem(X,below(N))
      <=> ( $lesseq(0,X)
          & $less(X,N) ) ) ) ).

tff(cardinal,type,
    cardinal: set1 > $int ).

tff(cardinal_empty,axiom,
    ! [S: set1] :
      ( ( cardinal(S) = 0 )
    <=> ! [X: $int] : ~ mem(X,S) ) ).

tff(cardinal_remove,axiom,
    ! [X: $int,S: set1] :
      ( mem(X,S)
     => ( cardinal(S) = $sum(1,cardinal(remove(X,S))) ) ) ).

tff(cardinal_below,axiom,
    ! [N: $int] :
      ( ( $lesseq(0,N)
        & $lesseq(N,size) )
     => ( ( $lesseq(0,N)
         => ( cardinal(below(N)) = N ) )
        & ( ~ $lesseq(0,N)
         => ( cardinal(below(N)) = 0 ) ) ) ) ).

tff(integer_size,axiom,
    $lesseq(n,size) ).

tff(map_int_lpmap_int_intrp,type,
    map_int_lpmap_int_intrp: $tType ).

tff(m,type,
    m: map_int_lpmap_int_intrp ).

tff(map_int_int,type,
    map_int_int: $tType ).

tff(t2tb,type,
    t2tb: map_int_int > uni ).

tff(t2tb_sort,axiom,
    ! [X: map_int_int] : sort(map(int,int),t2tb(X)) ).

tff(tb2t,type,
    tb2t: uni > map_int_int ).

tff(bridgeL,axiom,
    ! [I: map_int_int] : ( tb2t(t2tb(I)) = I ) ).

tff(bridgeR,axiom,
    ! [J: uni] : ( t2tb(tb2t(J)) = J ) ).

tff(t2tb1,type,
    t2tb1: map_int_lpmap_int_intrp > uni ).

tff(t2tb_sort1,axiom,
    ! [X: map_int_lpmap_int_intrp] : sort(map(int,map(int,int)),t2tb1(X)) ).

tff(tb2t1,type,
    tb2t1: uni > map_int_lpmap_int_intrp ).

tff(bridgeL1,axiom,
    ! [I: map_int_lpmap_int_intrp] : ( tb2t1(t2tb1(I)) = I ) ).

tff(bridgeR1,axiom,
    ! [J: uni] : ( t2tb1(tb2t1(J)) = J ) ).

tff(t2tb2,type,
    t2tb2: $int > uni ).

tff(t2tb_sort2,axiom,
    ! [X: $int] : sort(int,t2tb2(X)) ).

tff(tb2t2,type,
    tb2t2: uni > $int ).

tff(bridgeL2,axiom,
    ! [I: $int] : ( tb2t2(t2tb2(I)) = I ) ).

tff(bridgeR2,axiom,
    ! [J: uni] : ( t2tb2(tb2t2(J)) = J ) ).

tff(m_pos,axiom,
    ! [I: $int,J: $int] :
      ( ( $lesseq(0,I)
        & $less(I,n) )
     => ( ( $lesseq(0,J)
          & $less(J,n) )
       => $lesseq(0,tb2t2(get(int,int,get(map(int,int),int,t2tb1(m),t2tb2(I)),t2tb2(J)))) ) ) ).

tff(solution,type,
    solution: ( map_int_int * $int ) > $o ).

tff(solution_def,axiom,
    ! [S: map_int_int,I: $int] :
      ( solution(S,I)
    <=> ( ! [K: $int] :
            ( ( $lesseq(I,K)
              & $less(K,n) )
           => ( $lesseq(0,tb2t2(get(int,int,t2tb(S),t2tb2(K))))
              & $less(tb2t2(get(int,int,t2tb(S),t2tb2(K))),n) ) )
        & ! [K1: $int,K2: $int] :
            ( ( $lesseq(I,K1)
              & $less(K1,K2)
              & $less(K2,n) )
           => ( tb2t2(get(int,int,t2tb(S),t2tb2(K1))) != tb2t2(get(int,int,t2tb(S),t2tb2(K2))) ) ) ) ) ).

tff(f,type,
    f: ( map_int_int * $int ) > $int ).

tff(f_def,axiom,
    ! [S: map_int_int,I: $int] : ( f(S,I) = tb2t2(get(int,int,get(map(int,int),int,t2tb1(m),t2tb2(I)),get(int,int,t2tb(S),t2tb2(I)))) ) ).

tff(sum,type,
    sum: ( map_int_int * $int * $int ) > $int ).

tff(sum_def_empty,axiom,
    ! [C: map_int_int,I: $int,J: $int] :
      ( $lesseq(J,I)
     => ( sum(C,I,J) = 0 ) ) ).

tff(sum_def_non_empty,axiom,
    ! [C: map_int_int,I: $int,J: $int] :
      ( $less(I,J)
     => ( sum(C,I,J) = $sum(f(C,I),sum(C,$sum(I,1),J)) ) ) ).

tff(sum_right_extension,axiom,
    ! [C: map_int_int,I: $int,J: $int] :
      ( $less(I,J)
     => ( sum(C,I,J) = $sum(sum(C,I,$difference(J,1)),f(C,$difference(J,1))) ) ) ).

tff(sum_transitivity,axiom,
    ! [C: map_int_int,I: $int,K: $int,J: $int] :
      ( ( $lesseq(I,K)
        & $lesseq(K,J) )
     => ( sum(C,I,J) = $sum(sum(C,I,K),sum(C,K,J)) ) ) ).

tff(sum_eq,axiom,
    ! [C1: map_int_int,C2: map_int_int,I: $int,J: $int] :
      ( ! [K: $int] :
          ( ( $lesseq(I,K)
            & $less(K,J) )
         => ( f(C1,K) = f(C2,K) ) )
     => ( sum(C1,I,J) = sum(C2,I,J) ) ) ).

tff(sum_ind,axiom,
    ! [I: $int] :
      ( $less(I,n)
     => ! [J: $int,S: map_int_int] : ( sum(tb2t(set(int,int,t2tb(S),t2tb2(I),t2tb2(J))),I,n) = $sum(tb2t2(get(int,int,get(map(int,int),int,t2tb1(m),t2tb2(I)),t2tb2(J))),sum(S,$sum(I,1),n)) ) ) ).

tff(option,type,
    option: ty > ty ).

tff(none,type,
    none: ty > uni ).

tff(none_sort,axiom,
    ! [A: ty] : sort(option(A),none(A)) ).

tff(some,type,
    some: ( ty * uni ) > uni ).

tff(some_sort,axiom,
    ! [A: ty,X: uni] : sort(option(A),some(A,X)) ).

tff(match_option,type,
    match_option: ( ty * ty * uni * uni * uni ) > uni ).

tff(match_option_sort,axiom,
    ! [A: ty,A1: ty,X: uni,X1: uni,X2: uni] : sort(A1,match_option(A1,A,X,X1,X2)) ).

tff(match_option_None,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni] :
      ( sort(A1,Z)
     => ( match_option(A1,A,none(A),Z,Z1) = Z ) ) ).

tff(match_option_Some,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni,U: uni] :
      ( sort(A1,Z1)
     => ( match_option(A1,A,some(A,U),Z,Z1) = Z1 ) ) ).

tff(none_Some,axiom,
    ! [A: ty,V: uni] : ( none(A) != some(A,V) ) ).

tff(some_proj_1,type,
    some_proj_1: ( ty * uni ) > uni ).

tff(some_proj_1_sort,axiom,
    ! [A: ty,X: uni] : sort(A,some_proj_1(A,X)) ).

tff(some_proj_1_def,axiom,
    ! [A: ty,U: uni] :
      ( sort(A,U)
     => ( some_proj_1(A,some(A,U)) = U ) ) ).

tff(option_inversion,axiom,
    ! [A: ty,U: uni] :
      ( sort(option(A),U)
     => ( ( U = none(A) )
        | ( U = some(A,some_proj_1(A,U)) ) ) ) ).

tff(t,type,
    t: ( ty * ty ) > ty ).

tff(mk_t,type,
    mk_t: ( ty * ty * uni ) > uni ).

tff(mk_t_sort,axiom,
    ! [A: ty,B: ty,X: uni] : sort(t(A,B),mk_t(B,A,X)) ).

tff(contents1,type,
    contents1: ( ty * ty * uni ) > uni ).

tff(contents_sort1,axiom,
    ! [A: ty,B: ty,X: uni] : sort(map(A,option(B)),contents1(B,A,X)) ).

tff(contents_def1,axiom,
    ! [A: ty,B: ty,U: uni] :
      ( sort(map(A,option(B)),U)
     => ( contents1(B,A,mk_t(B,A,U)) = U ) ) ).

tff(t_inversion,axiom,
    ! [A: ty,B: ty,U: uni] :
      ( sort(t(A,B),U)
     => ( U = mk_t(B,A,contents1(B,A,U)) ) ) ).

tff(mixfix_lbrb,type,
    mixfix_lbrb: ( ty * ty * uni * uni ) > uni ).

tff(mixfix_lbrb_sort,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni] : sort(option(B),mixfix_lbrb(B,A,X,X1)) ).

tff(mixfix_lbrb_def,axiom,
    ! [A: ty,B: ty,H: uni,K: uni] : ( mixfix_lbrb(B,A,H,K) = get(option(B),A,contents1(B,A,H),K) ) ).

tff(tuple2,type,
    tuple2: ( ty * ty ) > ty ).

tff(tuple21,type,
    tuple21: ( ty * ty * uni * uni ) > uni ).

tff(tuple2_sort,axiom,
    ! [A: ty,A1: ty,X: uni,X1: uni] : sort(tuple2(A1,A),tuple21(A1,A,X,X1)) ).

tff(tuple2_proj_1,type,
    tuple2_proj_1: ( ty * ty * uni ) > uni ).

tff(tuple2_proj_1_sort,axiom,
    ! [A: ty,A1: ty,X: uni] : sort(A1,tuple2_proj_1(A1,A,X)) ).

tff(tuple2_proj_1_def,axiom,
    ! [A: ty,A1: ty,U: uni,U1: uni] :
      ( sort(A1,U)
     => ( tuple2_proj_1(A1,A,tuple21(A1,A,U,U1)) = U ) ) ).

tff(tuple2_proj_2,type,
    tuple2_proj_2: ( ty * ty * uni ) > uni ).

tff(tuple2_proj_2_sort,axiom,
    ! [A: ty,A1: ty,X: uni] : sort(A,tuple2_proj_2(A1,A,X)) ).

tff(tuple2_proj_2_def,axiom,
    ! [A: ty,A1: ty,U: uni,U1: uni] :
      ( sort(A,U1)
     => ( tuple2_proj_2(A1,A,tuple21(A1,A,U,U1)) = U1 ) ) ).

tff(tuple2_inversion,axiom,
    ! [A: ty,A1: ty,U: uni] :
      ( sort(tuple2(A1,A),U)
     => ( U = tuple21(A1,A,tuple2_proj_1(A1,A,U),tuple2_proj_2(A1,A,U)) ) ) ).

tff(lpintcm_setrp,type,
    lpintcm_setrp: $tType ).

tff(pre,type,
    pre: lpintcm_setrp > $o ).

tff(t2tb3,type,
    t2tb3: lpintcm_setrp > uni ).

tff(t2tb_sort3,axiom,
    ! [X: lpintcm_setrp] : sort(tuple2(int,set2),t2tb3(X)) ).

tff(tb2t3,type,
    tb2t3: uni > lpintcm_setrp ).

tff(bridgeL3,axiom,
    ! [I: lpintcm_setrp] : ( tb2t3(t2tb3(I)) = I ) ).

tff(bridgeR3,axiom,
    ! [J: uni] : ( t2tb3(tb2t3(J)) = J ) ).

tff(t2tb4,type,
    t2tb4: set1 > uni ).

tff(t2tb_sort4,axiom,
    ! [X: set1] : sort(set2,t2tb4(X)) ).

tff(tb2t4,type,
    tb2t4: uni > set1 ).

tff(bridgeL4,axiom,
    ! [I: set1] : ( tb2t4(t2tb4(I)) = I ) ).

tff(bridgeR4,axiom,
    ! [J: uni] :
      ( sort(set2,J)
     => ( t2tb4(tb2t4(J)) = J ) ) ).

tff(pre_def,axiom,
    ! [I: $int,C: set1] :
      ( pre(tb2t3(tuple21(int,set2,t2tb2(I),t2tb4(C))))
    <=> ( $lesseq(0,I)
        & $lesseq(I,n)
        & ( cardinal(C) = $difference(n,I) )
        & ! [K: $int] :
            ( mem(K,C)
           => ( $lesseq(0,K)
              & $less(K,n) ) ) ) ) ).

tff(lpintcm_map_int_intrp,type,
    lpintcm_map_int_intrp: $tType ).

tff(post,type,
    post: ( lpintcm_setrp * lpintcm_map_int_intrp ) > $o ).

tff(t2tb5,type,
    t2tb5: lpintcm_map_int_intrp > uni ).

tff(t2tb_sort5,axiom,
    ! [X: lpintcm_map_int_intrp] : sort(tuple2(int,map(int,int)),t2tb5(X)) ).

tff(tb2t5,type,
    tb2t5: uni > lpintcm_map_int_intrp ).

tff(bridgeL5,axiom,
    ! [I: lpintcm_map_int_intrp] : ( tb2t5(t2tb5(I)) = I ) ).

tff(bridgeR5,axiom,
    ! [J: uni] : ( t2tb5(tb2t5(J)) = J ) ).

tff(post_def,axiom,
    ! [I: $int,C: set1,R: $int,Sol: map_int_int] :
      ( post(tb2t3(tuple21(int,set2,t2tb2(I),t2tb4(C))),tb2t5(tuple21(int,map(int,int),t2tb2(R),t2tb(Sol))))
    <=> ( $lesseq(0,R)
        & solution(Sol,I)
        & ! [K: $int] :
            ( ( $lesseq(I,K)
              & $less(K,n) )
           => mem(tb2t2(get(int,int,t2tb(Sol),t2tb2(K))),C) )
        & ( R = sum(Sol,I,n) )
        & ! [S: map_int_int] :
            ( solution(S,I)
           => ( ! [K: $int] :
                  ( ( $lesseq(I,K)
                    & $less(K,n) )
                 => mem(tb2t2(get(int,int,t2tb(S),t2tb2(K))),C) )
             => $lesseq(sum(S,I,n),R) ) ) ) ) ).

tff(t18_lpintcm_setrp_lpintcm_map_int_intrp,type,
    t18_lpintcm_setrp_lpintcm_map_int_intrp: $tType ).

tff(inv,type,
    inv: t18_lpintcm_setrp_lpintcm_map_int_intrp > $o ).

tff(option_lpintcm_map_int_intrp,type,
    option_lpintcm_map_int_intrp: $tType ).

tff(t2tb6,type,
    t2tb6: option_lpintcm_map_int_intrp > uni ).

tff(t2tb_sort6,axiom,
    ! [X: option_lpintcm_map_int_intrp] : sort(option(tuple2(int,map(int,int))),t2tb6(X)) ).

tff(tb2t6,type,
    tb2t6: uni > option_lpintcm_map_int_intrp ).

tff(bridgeL6,axiom,
    ! [I: option_lpintcm_map_int_intrp] : ( tb2t6(t2tb6(I)) = I ) ).

tff(bridgeR6,axiom,
    ! [J: uni] : ( t2tb6(tb2t6(J)) = J ) ).

tff(t2tb7,type,
    t2tb7: t18_lpintcm_setrp_lpintcm_map_int_intrp > uni ).

tff(t2tb_sort7,axiom,
    ! [X: t18_lpintcm_setrp_lpintcm_map_int_intrp] : sort(t(tuple2(int,set2),tuple2(int,map(int,int))),t2tb7(X)) ).

tff(tb2t7,type,
    tb2t7: uni > t18_lpintcm_setrp_lpintcm_map_int_intrp ).

tff(bridgeL7,axiom,
    ! [I: t18_lpintcm_setrp_lpintcm_map_int_intrp] : ( tb2t7(t2tb7(I)) = I ) ).

tff(bridgeR7,axiom,
    ! [J: uni] : ( t2tb7(tb2t7(J)) = J ) ).

tff(inv_def,axiom,
    ! [T: t18_lpintcm_setrp_lpintcm_map_int_intrp] :
      ( inv(T)
    <=> ! [K: lpintcm_setrp,V: lpintcm_map_int_intrp] :
          ( ( tb2t6(mixfix_lbrb(tuple2(int,map(int,int)),tuple2(int,set2),t2tb7(T),t2tb3(K))) = tb2t6(some(tuple2(int,map(int,int)),t2tb5(V))) )
         => post(K,V) ) ) ).

tff(map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp,type,
    map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp: $tType ).

tff(t2tb8,type,
    t2tb8: map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp > uni ).

tff(t2tb_sort8,axiom,
    ! [X: map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp] : sort(map(tuple2(int,set2),option(tuple2(int,map(int,int)))),t2tb8(X)) ).

tff(tb2t8,type,
    tb2t8: uni > map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp ).

tff(bridgeL8,axiom,
    ! [I: map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp] : ( tb2t8(t2tb8(I)) = I ) ).

tff(bridgeR8,axiom,
    ! [J: uni] : ( t2tb8(tb2t8(J)) = J ) ).

tff(wP_parameter_maximum,conjecture,
    ! [I: $int,C: set1,Table: map_lpintcm_setrp_lpoption_lpintcm_map_int_intrprp] :
      ( ( pre(tb2t3(tuple21(int,set2,t2tb2(I),t2tb4(C))))
        & inv(tb2t7(mk_t(tuple2(int,map(int,int)),tuple2(int,set2),t2tb8(Table)))) )
     => ( ( I = n )
       => ( post(tb2t3(tuple21(int,set2,t2tb2(I),t2tb4(C))),tb2t5(tuple21(int,map(int,int),t2tb2(0),const(int,int,t2tb2(0)))))
          & inv(tb2t7(mk_t(tuple2(int,map(int,int)),tuple2(int,set2),t2tb8(Table)))) ) ) ) ).

%------------------------------------------------------------------------------

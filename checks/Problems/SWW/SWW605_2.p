%------------------------------------------------------------------------------
% File     : SWW605_2 : TPTP v9.0.0. Released v6.1.0.
% Domain   : Software Verification
% Problem  : Hashtbl impl-T-WP parameter resize
% Version  : Especial : Let and conditional terms encoded away.
% English  :

% Refs     : [Fil14] Filliatre (2014), Email to Geoff Sutcliffe
%          : [BF+]   Bobot et al. (URL), Toccata: Certified Programs and Cert
% Source   : [Fil14]
% Names    : hashtbl_impl-T-WP_parameter_resize [Fil14]

% Status   : Theorem
% Rating   : 0.38 v8.2.0, 0.50 v7.5.0, 0.60 v7.4.0, 0.50 v7.3.0, 0.17 v7.0.0, 0.57 v6.4.0, 0.33 v6.3.0, 0.71 v6.2.0, 0.62 v6.1.0
% Syntax   : Number of formulae    :  193 (  65 unt;  83 typ;   0 def)
%            Number of atoms       :  223 (  79 equ)
%            Maximal formula atoms :   38 (   1 avg)
%            Number of connectives :  129 (  16   ~;   7   |;  40   &)
%                                         (   6 <=>;  60  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   29 (   4 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number arithmetic     :  224 (  61 atm;  33 fun;  71 num;  59 var)
%            Number of types       :   14 (  12 usr;   1 ari)
%            Number of type conns  :  128 (  61   >;  67   *;   0   +;   0  <<)
%            Number of predicates  :    8 (   5 usr;   0 prp; 2-5 aty)
%            Number of functors    :   72 (  66 usr;  13 con; 0-5 aty)
%            Number of variables   :  285 ( 285   !;   0   ?; 285   :)
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

tff(match_bool_sort2,axiom,
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

tff(abs,type,
    abs1: $int > $int ).

tff(abs_def,axiom,
    ! [X: $int] :
      ( ( $lesseq(0,X)
       => ( abs1(X) = X ) )
      & ( ~ $lesseq(0,X)
       => ( abs1(X) = $uminus(X) ) ) ) ).

tff(abs_le,axiom,
    ! [X: $int,Y: $int] :
      ( $lesseq(abs1(X),Y)
    <=> ( $lesseq($uminus(Y),X)
        & $lesseq(X,Y) ) ) ).

tff(abs_pos,axiom,
    ! [X: $int] : $lesseq(0,abs1(X)) ).

tff(div,type,
    div1: ( $int * $int ) > $int ).

tff(mod,type,
    mod1: ( $int * $int ) > $int ).

tff(div_mod,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => ( X = $sum($product(Y,div1(X,Y)),mod1(X,Y)) ) ) ).

tff(div_bound,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(0,Y) )
     => ( $lesseq(0,div1(X,Y))
        & $lesseq(div1(X,Y),X) ) ) ).

tff(mod_bound,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => ( $less($uminus(abs1(Y)),mod1(X,Y))
        & $less(mod1(X,Y),abs1(Y)) ) ) ).

tff(div_sign_pos,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(0,Y) )
     => $lesseq(0,div1(X,Y)) ) ).

tff(div_sign_neg,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
        & $less(0,Y) )
     => $lesseq(div1(X,Y),0) ) ).

tff(mod_sign_pos,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & ( Y != 0 ) )
     => $lesseq(0,mod1(X,Y)) ) ).

tff(mod_sign_neg,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(X,0)
        & ( Y != 0 ) )
     => $lesseq(mod1(X,Y),0) ) ).

tff(rounds_toward_zero,axiom,
    ! [X: $int,Y: $int] :
      ( ( Y != 0 )
     => $lesseq(abs1($product(div1(X,Y),Y)),abs1(X)) ) ).

tff(div_1,axiom,
    ! [X: $int] : ( div1(X,1) = X ) ).

tff(mod_1,axiom,
    ! [X: $int] : ( mod1(X,1) = 0 ) ).

tff(div_inf,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(X,Y) )
     => ( div1(X,Y) = 0 ) ) ).

tff(mod_inf,axiom,
    ! [X: $int,Y: $int] :
      ( ( $lesseq(0,X)
        & $less(X,Y) )
     => ( mod1(X,Y) = X ) ) ).

tff(div_mult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( ( $less(0,X)
        & $lesseq(0,Y)
        & $lesseq(0,Z) )
     => ( div1($sum($product(X,Y),Z),X) = $sum(Y,div1(Z,X)) ) ) ).

tff(mod_mult,axiom,
    ! [X: $int,Y: $int,Z: $int] :
      ( ( $less(0,X)
        & $lesseq(0,Y)
        & $lesseq(0,Z) )
     => ( mod1($sum($product(X,Y),Z),X) = mod1(Z,X) ) ) ).

tff(option,type,
    option: ty > ty ).

tff(none,type,
    none: ty > uni ).

tff(none_sort2,axiom,
    ! [A: ty] : sort1(option(A),none(A)) ).

tff(some,type,
    some: ( ty * uni ) > uni ).

tff(some_sort2,axiom,
    ! [A: ty,X: uni] : sort1(option(A),some(A,X)) ).

tff(match_option,type,
    match_option1: ( ty * ty * uni * uni * uni ) > uni ).

tff(match_option_sort2,axiom,
    ! [A: ty,A1: ty,X: uni,X1: uni,X2: uni] : sort1(A1,match_option1(A1,A,X,X1,X2)) ).

tff(match_option_None1,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni] :
      ( sort1(A1,Z)
     => ( match_option1(A1,A,none(A),Z,Z1) = Z ) ) ).

tff(match_option_Some1,axiom,
    ! [A: ty,A1: ty,Z: uni,Z1: uni,U: uni] :
      ( sort1(A1,Z1)
     => ( match_option1(A1,A,some(A,U),Z,Z1) = Z1 ) ) ).

tff(none_Some1,axiom,
    ! [A: ty,V: uni] : ( none(A) != some(A,V) ) ).

tff(some_proj_1,type,
    some_proj_11: ( ty * uni ) > uni ).

tff(some_proj_1_sort2,axiom,
    ! [A: ty,X: uni] : sort1(A,some_proj_11(A,X)) ).

tff(some_proj_1_def1,axiom,
    ! [A: ty,U: uni] :
      ( sort1(A,U)
     => ( some_proj_11(A,some(A,U)) = U ) ) ).

tff(option_inversion1,axiom,
    ! [A: ty,U: uni] :
      ( sort1(option(A),U)
     => ( ( U = none(A) )
        | ( U = some(A,some_proj_11(A,U)) ) ) ) ).

tff(list,type,
    list: ty > ty ).

tff(nil,type,
    nil: ty > uni ).

tff(nil_sort2,axiom,
    ! [A: ty] : sort1(list(A),nil(A)) ).

tff(cons,type,
    cons: ( ty * uni * uni ) > uni ).

tff(cons_sort2,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(list(A),cons(A,X,X1)) ).

tff(match_list,type,
    match_list1: ( ty * ty * uni * uni * uni ) > uni ).

tff(match_list_sort2,axiom,
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

tff(cons_proj_1_sort2,axiom,
    ! [A: ty,X: uni] : sort1(A,cons_proj_11(A,X)) ).

tff(cons_proj_1_def1,axiom,
    ! [A: ty,U: uni,U1: uni] :
      ( sort1(A,U)
     => ( cons_proj_11(A,cons(A,U,U1)) = U ) ) ).

tff(cons_proj_2,type,
    cons_proj_21: ( ty * uni ) > uni ).

tff(cons_proj_2_sort2,axiom,
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

tff(map,type,
    map: ( ty * ty ) > ty ).

tff(get,type,
    get: ( ty * ty * uni * uni ) > uni ).

tff(get_sort4,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni] : sort1(B,get(B,A,X,X1)) ).

tff(set,type,
    set: ( ty * ty * uni * uni * uni ) > uni ).

tff(set_sort4,axiom,
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

tff(const_sort2,axiom,
    ! [A: ty,B: ty,X: uni] : sort1(map(A,B),const(B,A,X)) ).

tff(const,axiom,
    ! [A: ty,B: ty,B1: uni,A1: uni] :
      ( sort1(B,B1)
     => ( get(B,A,const(B,A,B1),A1) = B1 ) ) ).

tff(array,type,
    array: ty > ty ).

tff(mk_array,type,
    mk_array1: ( ty * $int * uni ) > uni ).

tff(mk_array_sort2,axiom,
    ! [A: ty,X: $int,X1: uni] : sort1(array(A),mk_array1(A,X,X1)) ).

tff(length,type,
    length1: ( ty * uni ) > $int ).

tff(length_def1,axiom,
    ! [A: ty,U: $int,U1: uni] : ( length1(A,mk_array1(A,U,U1)) = U ) ).

tff(elts,type,
    elts: ( ty * uni ) > uni ).

tff(elts_sort2,axiom,
    ! [A: ty,X: uni] : sort1(map(int,A),elts(A,X)) ).

tff(elts_def1,axiom,
    ! [A: ty,U: $int,U1: uni] :
      ( sort1(map(int,A),U1)
     => ( elts(A,mk_array1(A,U,U1)) = U1 ) ) ).

tff(array_inversion1,axiom,
    ! [A: ty,U: uni] : ( U = mk_array1(A,length1(A,U),elts(A,U)) ) ).

tff(get1,type,
    get2: ( ty * uni * $int ) > uni ).

tff(get_sort5,axiom,
    ! [A: ty,X: uni,X1: $int] : sort1(A,get2(A,X,X1)) ).

tff(t2tb,type,
    t2tb: $int > uni ).

tff(t2tb_sort8,axiom,
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

tff(set_sort5,axiom,
    ! [A: ty,X: uni,X1: $int,X2: uni] : sort1(array(A),set2(A,X,X1,X2)) ).

tff(set_def,axiom,
    ! [A: ty,A1: uni,I: $int,V: uni] : ( set2(A,A1,I,V) = mk_array1(A,length1(A,A1),set(A,int,elts(A,A1),t2tb(I),V)) ) ).

tff(make,type,
    make1: ( ty * $int * uni ) > uni ).

tff(make_sort2,axiom,
    ! [A: ty,X: $int,X1: uni] : sort1(array(A),make1(A,X,X1)) ).

tff(make_def,axiom,
    ! [A: ty,N: $int,V: uni] : ( make1(A,N,V) = mk_array1(A,N,const(A,int,V)) ) ).

tff(key,type,
    key1: $tType ).

tff(key1,type,
    key: ty ).

tff(hash,type,
    hash1: key1 > $int ).

tff(hash_nonneg,axiom,
    ! [K: key1] : $lesseq(0,hash1(K)) ).

tff(bucket,type,
    bucket1: ( key1 * $int ) > $int ).

tff(bucket_def,axiom,
    ! [K: key1,N: $int] : ( bucket1(K,N) = mod1(hash1(K),N) ) ).

tff(bucket_bounds,axiom,
    ! [N: $int] :
      ( $less(0,N)
     => ! [K: key1] :
          ( $lesseq(0,bucket1(K,N))
          & $less(bucket1(K,N),N) ) ) ).

tff(tuple2,type,
    tuple2: ( ty * ty ) > ty ).

tff(tuple21,type,
    tuple21: ( ty * ty * uni * uni ) > uni ).

tff(tuple2_sort2,axiom,
    ! [A: ty,A1: ty,X: uni,X1: uni] : sort1(tuple2(A1,A),tuple21(A1,A,X,X1)) ).

tff(tuple2_proj_1,type,
    tuple2_proj_11: ( ty * ty * uni ) > uni ).

tff(tuple2_proj_1_sort2,axiom,
    ! [A: ty,A1: ty,X: uni] : sort1(A1,tuple2_proj_11(A1,A,X)) ).

tff(tuple2_proj_1_def1,axiom,
    ! [A: ty,A1: ty,U: uni,U1: uni] :
      ( sort1(A1,U)
     => ( tuple2_proj_11(A1,A,tuple21(A1,A,U,U1)) = U ) ) ).

tff(tuple2_proj_2,type,
    tuple2_proj_21: ( ty * ty * uni ) > uni ).

tff(tuple2_proj_2_sort2,axiom,
    ! [A: ty,A1: ty,X: uni] : sort1(A,tuple2_proj_21(A1,A,X)) ).

tff(tuple2_proj_2_def1,axiom,
    ! [A: ty,A1: ty,U: uni,U1: uni] :
      ( sort1(A,U1)
     => ( tuple2_proj_21(A1,A,tuple21(A1,A,U,U1)) = U1 ) ) ).

tff(tuple2_inversion1,axiom,
    ! [A: ty,A1: ty,U: uni] :
      ( sort1(tuple2(A1,A),U)
     => ( U = tuple21(A1,A,tuple2_proj_11(A1,A,U),tuple2_proj_21(A1,A,U)) ) ) ).

tff(in_data,type,
    in_data1: ( ty * key1 * uni * uni ) > $o ).

tff(t2tb1,type,
    t2tb1: key1 > uni ).

tff(t2tb_sort9,axiom,
    ! [X: key1] : sort1(key,t2tb1(X)) ).

tff(tb2t1,type,
    tb2t1: uni > key1 ).

tff(bridgeL1,axiom,
    ! [I: key1] : ( tb2t1(t2tb1(I)) = I ) ).

tff(bridgeR1,axiom,
    ! [J: uni] :
      ( sort1(key,J)
     => ( t2tb1(tb2t1(J)) = J ) ) ).

tff(in_data_def,axiom,
    ! [A: ty,K: key1,V: uni,D: uni] :
      ( in_data1(A,K,V,D)
    <=> mem(tuple2(key,A),tuple21(key,A,t2tb1(K),V),get2(list(tuple2(key,A)),D,bucket1(K,length1(list(tuple2(key,A)),D)))) ) ).

tff(good_data,type,
    good_data1: ( ty * key1 * uni * uni * uni ) > $o ).

tff(good_data_def,axiom,
    ! [A: ty,K: key1,V: uni,M: uni,D: uni] :
      ( good_data1(A,K,V,M,D)
    <=> ( ( get(option(A),key,M,t2tb1(K)) = some(A,V) )
      <=> in_data1(A,K,V,D) ) ) ).

tff(good_hash,type,
    good_hash1: ( ty * uni * $int ) > $o ).

tff(good_hash_def,axiom,
    ! [A: ty,D: uni,I: $int] :
      ( ( good_hash1(A,D,I)
       => ! [K: key1,V: uni] :
            ( mem(tuple2(key,A),tuple21(key,A,t2tb1(K),V),get2(list(tuple2(key,A)),D,I))
           => ( bucket1(K,length1(list(tuple2(key,A)),D)) = I ) ) )
      & ( ! [K: key1,V: uni] :
            ( sort1(A,V)
           => ( mem(tuple2(key,A),tuple21(key,A,t2tb1(K),V),get2(list(tuple2(key,A)),D,I))
             => ( bucket1(K,length1(list(tuple2(key,A)),D)) = I ) ) )
       => good_hash1(A,D,I) ) ) ).

tff(t,type,
    t: ty > ty ).

tff(mk_t,type,
    mk_t1: ( ty * $int * uni * uni ) > uni ).

tff(mk_t_sort2,axiom,
    ! [A: ty,X: $int,X1: uni,X2: uni] : sort1(t(A),mk_t1(A,X,X1,X2)) ).

tff(size,type,
    size1: ( ty * uni ) > $int ).

tff(size_def1,axiom,
    ! [A: ty,U: $int,U1: uni,U2: uni] : ( size1(A,mk_t1(A,U,U1,U2)) = U ) ).

tff(data,type,
    data: ( ty * uni ) > uni ).

tff(data_sort2,axiom,
    ! [A: ty,X: uni] : sort1(array(list(tuple2(key,A))),data(A,X)) ).

tff(data_def1,axiom,
    ! [A: ty,U: $int,U1: uni,U2: uni] : ( data(A,mk_t1(A,U,U1,U2)) = U1 ) ).

tff(view,type,
    view: ( ty * uni ) > uni ).

tff(view_sort2,axiom,
    ! [A: ty,X: uni] : sort1(map(key,option(A)),view(A,X)) ).

tff(view_def1,axiom,
    ! [A: ty,U: $int,U1: uni,U2: uni] :
      ( sort1(map(key,option(A)),U2)
     => ( view(A,mk_t1(A,U,U1,U2)) = U2 ) ) ).

tff(t_inversion1,axiom,
    ! [A: ty,U: uni] : ( U = mk_t1(A,size1(A,U),data(A,U),view(A,U)) ) ).

tff(a,type,
    a1: $tType ).

tff(a1,type,
    a: ty ).

tff(map_int_lplist_lpkeycm_a1rprp,type,
    map_int_lplist_lpkeycm_a1rprp: $tType ).

tff(t2tb2,type,
    t2tb2: map_int_lplist_lpkeycm_a1rprp > uni ).

tff(t2tb_sort10,axiom,
    ! [X: map_int_lplist_lpkeycm_a1rprp] : sort1(map(int,list(tuple2(key,a))),t2tb2(X)) ).

tff(tb2t2,type,
    tb2t2: uni > map_int_lplist_lpkeycm_a1rprp ).

tff(bridgeL2,axiom,
    ! [I: map_int_lplist_lpkeycm_a1rprp] : ( tb2t2(t2tb2(I)) = I ) ).

tff(bridgeR2,axiom,
    ! [J: uni] : ( t2tb2(tb2t2(J)) = J ) ).

tff(map_key_lpoption_a1rp,type,
    map_key_lpoption_a1rp: $tType ).

tff(t2tb3,type,
    t2tb3: map_key_lpoption_a1rp > uni ).

tff(t2tb_sort11,axiom,
    ! [X: map_key_lpoption_a1rp] : sort1(map(key,option(a)),t2tb3(X)) ).

tff(tb2t3,type,
    tb2t3: uni > map_key_lpoption_a1rp ).

tff(bridgeL3,axiom,
    ! [I: map_key_lpoption_a1rp] : ( tb2t3(t2tb3(I)) = I ) ).

tff(bridgeR3,axiom,
    ! [J: uni] :
      ( sort1(map(key,option(a)),J)
     => ( t2tb3(tb2t3(J)) = J ) ) ).

tff(option_a1,type,
    option_a1: $tType ).

tff(t2tb4,type,
    t2tb4: option_a1 > uni ).

tff(t2tb_sort12,axiom,
    ! [X: option_a1] : sort1(option(a),t2tb4(X)) ).

tff(tb2t4,type,
    tb2t4: uni > option_a1 ).

tff(bridgeL4,axiom,
    ! [I: option_a1] : ( tb2t4(t2tb4(I)) = I ) ).

tff(bridgeR4,axiom,
    ! [J: uni] :
      ( sort1(option(a),J)
     => ( t2tb4(tb2t4(J)) = J ) ) ).

tff(array_lplist_lpkeycm_a1rprp,type,
    array_lplist_lpkeycm_a1rprp: $tType ).

tff(t2tb5,type,
    t2tb5: array_lplist_lpkeycm_a1rprp > uni ).

tff(t2tb_sort13,axiom,
    ! [X: array_lplist_lpkeycm_a1rprp] : sort1(array(list(tuple2(key,a))),t2tb5(X)) ).

tff(tb2t5,type,
    tb2t5: uni > array_lplist_lpkeycm_a1rprp ).

tff(bridgeL5,axiom,
    ! [I: array_lplist_lpkeycm_a1rprp] : ( tb2t5(t2tb5(I)) = I ) ).

tff(bridgeR5,axiom,
    ! [J: uni] : ( t2tb5(tb2t5(J)) = J ) ).

tff(list_lpkeycm_a1rp,type,
    list_lpkeycm_a1rp: $tType ).

tff(t2tb6,type,
    t2tb6: list_lpkeycm_a1rp > uni ).

tff(t2tb_sort14,axiom,
    ! [X: list_lpkeycm_a1rp] : sort1(list(tuple2(key,a)),t2tb6(X)) ).

tff(tb2t6,type,
    tb2t6: uni > list_lpkeycm_a1rp ).

tff(bridgeL6,axiom,
    ! [I: list_lpkeycm_a1rp] : ( tb2t6(t2tb6(I)) = I ) ).

tff(bridgeR6,axiom,
    ! [J: uni] : ( t2tb6(tb2t6(J)) = J ) ).

tff(lpkeycm_a1rp,type,
    lpkeycm_a1rp: $tType ).

tff(t2tb8,type,
    t2tb8: lpkeycm_a1rp > uni ).

tff(t2tb_sort15,axiom,
    ! [X: lpkeycm_a1rp] : sort1(tuple2(key,a),t2tb8(X)) ).

tff(tb2t8,type,
    tb2t8: uni > lpkeycm_a1rp ).

tff(bridgeL8,axiom,
    ! [I: lpkeycm_a1rp] : ( tb2t8(t2tb8(I)) = I ) ).

tff(bridgeR8,axiom,
    ! [J: uni] :
      ( sort1(tuple2(key,a),J)
     => ( t2tb8(tb2t8(J)) = J ) ) ).

tff(t2tb7,type,
    t2tb7: a1 > uni ).

tff(t2tb_sort16,axiom,
    ! [X: a1] : sort1(a,t2tb7(X)) ).

tff(tb2t7,type,
    tb2t7: uni > a1 ).

tff(bridgeL7,axiom,
    ! [I: a1] : ( tb2t7(t2tb7(I)) = I ) ).

tff(bridgeR7,axiom,
    ! [J: uni] :
      ( sort1(a,J)
     => ( t2tb7(tb2t7(J)) = J ) ) ).

tff(wP_parameter_resize,conjecture,
    ! [H: $int,H1: map_int_lplist_lpkeycm_a1rprp,H2: map_key_lpoption_a1rp] :
      ( ( $less(0,H)
        & ! [I: $int] :
            ( ( $lesseq(0,I)
              & $less(I,H) )
           => good_hash1(a,mk_array1(list(tuple2(key,a)),H,t2tb2(H1)),I) )
        & ! [K: key1,V: a1] : good_data1(a,K,t2tb7(V),t2tb3(H2),mk_array1(list(tuple2(key,a)),H,t2tb2(H1)))
        & $lesseq(0,H) )
     => ( $lesseq(0,$sum($product(2,H),1))
       => ( $lesseq(0,$sum($product(2,H),1))
         => ! [I: $int,L: list_lpkeycm_a1rp,Ndata: map_int_lplist_lpkeycm_a1rprp,Rho: map_key_lpoption_a1rp,Rho1: $int,Rho2: map_int_lplist_lpkeycm_a1rprp] :
              ( ( $less(0,Rho1)
                & ! [I1: $int] :
                    ( ( $lesseq(0,I1)
                      & $less(I1,Rho1) )
                   => good_hash1(a,mk_array1(list(tuple2(key,a)),Rho1,t2tb2(Rho2)),I1) )
                & ! [K: key1,V: a1] : good_data1(a,K,t2tb7(V),t2tb3(Rho),mk_array1(list(tuple2(key,a)),Rho1,t2tb2(Rho2)))
                & $lesseq(0,Rho1)
                & $lesseq(0,$sum($product(2,H),1))
                & ! [K: key1,V: a1] :
                    ( mem(tuple2(key,a),tuple21(key,a,t2tb1(K),t2tb7(V)),t2tb6(L))
                   => ( bucket1(K,H) = I ) )
                & ! [J: $int] :
                    ( ( $lesseq(0,J)
                      & $less(J,$sum($product(2,H),1)) )
                   => good_hash1(a,mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata)),J) )
                & ! [K: key1,V: a1] :
                    ( ( $lesseq(0,bucket1(K,H))
                      & $less(bucket1(K,H),I)
                      & good_data1(a,K,t2tb7(V),t2tb3(Rho),mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata))) )
                    | ( ~ ( $lesseq(0,bucket1(K,H))
                          & $less(bucket1(K,H),I) )
                      & ( ( ( bucket1(K,H) = I )
                          & ( ( tb2t4(get(option(a),key,t2tb3(Rho),t2tb1(K))) = tb2t4(some(a,t2tb7(V))) )
                          <=> ( mem(tuple2(key,a),tuple21(key,a,t2tb1(K),t2tb7(V)),t2tb6(L))
                              | in_data1(a,K,t2tb7(V),mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata))) ) ) )
                        | ( ( bucket1(K,H) != I )
                          & ~ in_data1(a,K,t2tb7(V),mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata))) ) ) ) ) )
             => ( ( L = tb2t6(nil(tuple2(key,a))) )
               => ! [K: key1,V: a1] :
                    ( ( ( $lesseq(0,bucket1(K,H))
                        & $lesseq(bucket1(K,H),I) )
                     => good_data1(a,K,t2tb7(V),t2tb3(Rho),mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata))) )
                    & ( ~ ( $lesseq(0,bucket1(K,H))
                          & $lesseq(bucket1(K,H),I) )
                     => ~ in_data1(a,K,t2tb7(V),mk_array1(list(tuple2(key,a)),$sum($product(2,H),1),t2tb2(Ndata))) ) ) ) ) ) ) ) ).

%------------------------------------------------------------------------------

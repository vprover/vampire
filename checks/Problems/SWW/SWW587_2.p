%------------------------------------------------------------------------------
% File     : SWW587_2 : TPTP v9.0.0. Released v6.1.0.
% Domain   : Software Verification
% Problem  : Dijkstra-T-WP parameter shortest path code
% Version  : Especial : Let and conditional terms encoded away.
% English  :

% Refs     : [Fil14] Filliatre (2014), Email to Geoff Sutcliffe
%          : [BF+]   Bobot et al. (URL), Toccata: Certified Programs and Cert
% Source   : [Fil14]
% Names    : dijkstra-T-WP_parameter_shortest_path_code [Fil14]

% Status   : Theorem
% Rating   : 0.50 v8.2.0, 0.62 v7.5.0, 0.60 v7.4.0, 0.62 v7.3.0, 0.50 v7.0.0, 0.43 v6.4.0, 0.33 v6.3.0, 0.57 v6.2.0, 1.00 v6.1.0
% Syntax   : Number of formulae    :  135 (  35 unt;  57 typ;   0 def)
%            Number of atoms       :  288 (  67 equ)
%            Maximal formula atoms :   90 (   2 avg)
%            Number of connectives :  236 (  26   ~;  19   |;  68   &)
%                                         (  17 <=>; 106  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   46 (   6 avg)
%            Maximal term depth    :    8 (   1 avg)
%            Number arithmetic     :   76 (  23 atm;  18 fun;  16 num;  19 var)
%            Number of types       :    9 (   7 usr;   1 ari)
%            Number of type conns  :   95 (  40   >;  55   *;   0   +;   0  <<)
%            Number of predicates  :   16 (  12 usr;   1 prp; 0-6 aty)
%            Number of functors    :   43 (  38 usr;  12 con; 0-5 aty)
%            Number of variables   :  273 ( 264   !;   9   ?; 273   :)
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

tff(ref,type,
    ref: ty > ty ).

tff(mk_ref,type,
    mk_ref: ( ty * uni ) > uni ).

tff(mk_ref_sort1,axiom,
    ! [A: ty,X: uni] : sort1(ref(A),mk_ref(A,X)) ).

tff(contents,type,
    contents: ( ty * uni ) > uni ).

tff(contents_sort1,axiom,
    ! [A: ty,X: uni] : sort1(A,contents(A,X)) ).

tff(contents_def1,axiom,
    ! [A: ty,U: uni] :
      ( sort1(A,U)
     => ( contents(A,mk_ref(A,U)) = U ) ) ).

tff(ref_inversion1,axiom,
    ! [A: ty,U: uni] :
      ( sort1(ref(A),U)
     => ( U = mk_ref(A,contents(A,U)) ) ) ).

tff(set,type,
    set: ty > ty ).

tff(mem,type,
    mem: ( ty * uni * uni ) > $o ).

tff(infix_eqeq,type,
    infix_eqeq: ( ty * uni * uni ) > $o ).

tff(infix_eqeq_def,axiom,
    ! [A: ty,S1: uni,S2: uni] :
      ( ( infix_eqeq(A,S1,S2)
       => ! [X: uni] :
            ( mem(A,X,S1)
          <=> mem(A,X,S2) ) )
      & ( ! [X: uni] :
            ( sort1(A,X)
           => ( mem(A,X,S1)
            <=> mem(A,X,S2) ) )
       => infix_eqeq(A,S1,S2) ) ) ).

tff(extensionality,axiom,
    ! [A: ty,S1: uni,S2: uni] :
      ( sort1(set(A),S1)
     => ( sort1(set(A),S2)
       => ( infix_eqeq(A,S1,S2)
         => ( S1 = S2 ) ) ) ) ).

tff(subset,type,
    subset: ( ty * uni * uni ) > $o ).

tff(subset_def,axiom,
    ! [A: ty,S1: uni,S2: uni] :
      ( ( subset(A,S1,S2)
       => ! [X: uni] :
            ( mem(A,X,S1)
           => mem(A,X,S2) ) )
      & ( ! [X: uni] :
            ( sort1(A,X)
           => ( mem(A,X,S1)
             => mem(A,X,S2) ) )
       => subset(A,S1,S2) ) ) ).

tff(subset_refl,axiom,
    ! [A: ty,S: uni] : subset(A,S,S) ).

tff(subset_trans,axiom,
    ! [A: ty,S1: uni,S2: uni,S3: uni] :
      ( subset(A,S1,S2)
     => ( subset(A,S2,S3)
       => subset(A,S1,S3) ) ) ).

tff(empty,type,
    empty: ty > uni ).

tff(empty_sort1,axiom,
    ! [A: ty] : sort1(set(A),empty(A)) ).

tff(is_empty,type,
    is_empty: ( ty * uni ) > $o ).

tff(is_empty_def,axiom,
    ! [A: ty,S: uni] :
      ( ( is_empty(A,S)
       => ! [X: uni] : ~ mem(A,X,S) )
      & ( ! [X: uni] :
            ( sort1(A,X)
           => ~ mem(A,X,S) )
       => is_empty(A,S) ) ) ).

tff(empty_def1,axiom,
    ! [A: ty] : is_empty(A,empty(A)) ).

tff(mem_empty,axiom,
    ! [A: ty,X: uni] :
      ( mem(A,X,empty(A))
    <=> $false ) ).

tff(add,type,
    add: ( ty * uni * uni ) > uni ).

tff(add_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(set(A),add(A,X,X1)) ).

tff(add_def1,axiom,
    ! [A: ty,X: uni,Y: uni] :
      ( sort1(A,X)
     => ( sort1(A,Y)
       => ! [S: uni] :
            ( mem(A,X,add(A,Y,S))
          <=> ( ( X = Y )
              | mem(A,X,S) ) ) ) ) ).

tff(remove,type,
    remove: ( ty * uni * uni ) > uni ).

tff(remove_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(set(A),remove(A,X,X1)) ).

tff(remove_def1,axiom,
    ! [A: ty,X: uni,Y: uni,S: uni] :
      ( sort1(A,X)
     => ( sort1(A,Y)
       => ( mem(A,X,remove(A,Y,S))
        <=> ( ( X != Y )
            & mem(A,X,S) ) ) ) ) ).

tff(add_remove,axiom,
    ! [A: ty,X: uni,S: uni] :
      ( sort1(set(A),S)
     => ( mem(A,X,S)
       => ( add(A,X,remove(A,X,S)) = S ) ) ) ).

tff(remove_add,axiom,
    ! [A: ty,X: uni,S: uni] : ( remove(A,X,add(A,X,S)) = remove(A,X,S) ) ).

tff(subset_remove,axiom,
    ! [A: ty,X: uni,S: uni] : subset(A,remove(A,X,S),S) ).

tff(union,type,
    union: ( ty * uni * uni ) > uni ).

tff(union_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(set(A),union(A,X,X1)) ).

tff(union_def1,axiom,
    ! [A: ty,S1: uni,S2: uni,X: uni] :
      ( mem(A,X,union(A,S1,S2))
    <=> ( mem(A,X,S1)
        | mem(A,X,S2) ) ) ).

tff(inter,type,
    inter: ( ty * uni * uni ) > uni ).

tff(inter_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(set(A),inter(A,X,X1)) ).

tff(inter_def1,axiom,
    ! [A: ty,S1: uni,S2: uni,X: uni] :
      ( mem(A,X,inter(A,S1,S2))
    <=> ( mem(A,X,S1)
        & mem(A,X,S2) ) ) ).

tff(diff,type,
    diff: ( ty * uni * uni ) > uni ).

tff(diff_sort1,axiom,
    ! [A: ty,X: uni,X1: uni] : sort1(set(A),diff(A,X,X1)) ).

tff(diff_def1,axiom,
    ! [A: ty,S1: uni,S2: uni,X: uni] :
      ( mem(A,X,diff(A,S1,S2))
    <=> ( mem(A,X,S1)
        & ~ mem(A,X,S2) ) ) ).

tff(subset_diff,axiom,
    ! [A: ty,S1: uni,S2: uni] : subset(A,diff(A,S1,S2),S1) ).

tff(choose,type,
    choose: ( ty * uni ) > uni ).

tff(choose_sort1,axiom,
    ! [A: ty,X: uni] : sort1(A,choose(A,X)) ).

tff(choose_def,axiom,
    ! [A: ty,S: uni] :
      ( ~ is_empty(A,S)
     => mem(A,choose(A,S),S) ) ).

tff(cardinal,type,
    cardinal1: ( ty * uni ) > $int ).

tff(cardinal_nonneg,axiom,
    ! [A: ty,S: uni] : $lesseq(0,cardinal1(A,S)) ).

tff(cardinal_empty,axiom,
    ! [A: ty,S: uni] :
      ( ( cardinal1(A,S) = 0 )
    <=> is_empty(A,S) ) ).

tff(cardinal_add,axiom,
    ! [A: ty,X: uni,S: uni] :
      ( ~ mem(A,X,S)
     => ( cardinal1(A,add(A,X,S)) = $sum(1,cardinal1(A,S)) ) ) ).

tff(cardinal_remove,axiom,
    ! [A: ty,X: uni,S: uni] :
      ( mem(A,X,S)
     => ( cardinal1(A,S) = $sum(1,cardinal1(A,remove(A,X,S))) ) ) ).

tff(cardinal_subset,axiom,
    ! [A: ty,S1: uni,S2: uni] :
      ( subset(A,S1,S2)
     => $lesseq(cardinal1(A,S1),cardinal1(A,S2)) ) ).

tff(cardinal1,axiom,
    ! [A: ty,S: uni] :
      ( ( cardinal1(A,S) = 1 )
     => ! [X: uni] :
          ( sort1(A,X)
         => ( mem(A,X,S)
           => ( X = choose(A,S) ) ) ) ) ).

tff(map,type,
    map: ( ty * ty ) > ty ).

tff(get,type,
    get: ( ty * ty * uni * uni ) > uni ).

tff(get_sort1,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni] : sort1(B,get(B,A,X,X1)) ).

tff(set1,type,
    set1: ( ty * ty * uni * uni * uni ) > uni ).

tff(set_sort1,axiom,
    ! [A: ty,B: ty,X: uni,X1: uni,X2: uni] : sort1(map(A,B),set1(B,A,X,X1,X2)) ).

tff(select_eq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni,B1: uni] :
      ( sort1(B,B1)
     => ( ( A1 = A2 )
       => ( get(B,A,set1(B,A,M,A1,B1),A2) = B1 ) ) ) ).

tff(select_neq,axiom,
    ! [A: ty,B: ty,M: uni,A1: uni,A2: uni] :
      ( sort1(A,A1)
     => ( sort1(A,A2)
       => ! [B1: uni] :
            ( ( A1 != A2 )
           => ( get(B,A,set1(B,A,M,A1,B1),A2) = get(B,A,M,A2) ) ) ) ) ).

tff(const1,type,
    const: ( ty * ty * uni ) > uni ).

tff(const_sort1,axiom,
    ! [A: ty,B: ty,X: uni] : sort1(map(A,B),const(B,A,X)) ).

tff(const,axiom,
    ! [A: ty,B: ty,B1: uni,A1: uni] :
      ( sort1(B,B1)
     => ( get(B,A,const(B,A,B1),A1) = B1 ) ) ).

tff(vertex,type,
    vertex1: $tType ).

tff(vertex1,type,
    vertex: ty ).

tff(set_vertex,type,
    set_vertex: $tType ).

tff(v,type,
    v1: set_vertex ).

tff(g_succ,type,
    g_succ1: vertex1 > set_vertex ).

tff(t2tb,type,
    t2tb: set_vertex > uni ).

tff(t2tb_sort,axiom,
    ! [X: set_vertex] : sort1(set(vertex),t2tb(X)) ).

tff(tb2t,type,
    tb2t: uni > set_vertex ).

tff(bridgeL,axiom,
    ! [I: set_vertex] : ( tb2t(t2tb(I)) = I ) ).

tff(bridgeR,axiom,
    ! [J: uni] :
      ( sort1(set(vertex),J)
     => ( t2tb(tb2t(J)) = J ) ) ).

tff(g_succ_sound,axiom,
    ! [X: vertex1] : subset(vertex,t2tb(g_succ1(X)),t2tb(v1)) ).

tff(weight,type,
    weight1: ( vertex1 * vertex1 ) > $int ).

tff(weight_nonneg,axiom,
    ! [X: vertex1,Y: vertex1] : $lesseq(0,weight1(X,Y)) ).

tff(map_vertex_int,type,
    map_vertex_int: $tType ).

tff(min,type,
    min1: ( vertex1 * set_vertex * map_vertex_int ) > $o ).

tff(t2tb1,type,
    t2tb1: map_vertex_int > uni ).

tff(t2tb_sort1,axiom,
    ! [X: map_vertex_int] : sort1(map(vertex,int),t2tb1(X)) ).

tff(tb2t1,type,
    tb2t1: uni > map_vertex_int ).

tff(bridgeL1,axiom,
    ! [I: map_vertex_int] : ( tb2t1(t2tb1(I)) = I ) ).

tff(bridgeR1,axiom,
    ! [J: uni] : ( t2tb1(tb2t1(J)) = J ) ).

tff(t2tb2,type,
    t2tb2: vertex1 > uni ).

tff(t2tb_sort2,axiom,
    ! [X: vertex1] : sort1(vertex,t2tb2(X)) ).

tff(tb2t2,type,
    tb2t2: uni > vertex1 ).

tff(bridgeL2,axiom,
    ! [I: vertex1] : ( tb2t2(t2tb2(I)) = I ) ).

tff(bridgeR2,axiom,
    ! [J: uni] :
      ( sort1(vertex,J)
     => ( t2tb2(tb2t2(J)) = J ) ) ).

tff(t2tb3,type,
    t2tb3: $int > uni ).

tff(t2tb_sort3,axiom,
    ! [X: $int] : sort1(int,t2tb3(X)) ).

tff(tb2t3,type,
    tb2t3: uni > $int ).

tff(bridgeL3,axiom,
    ! [I: $int] : ( tb2t3(t2tb3(I)) = I ) ).

tff(bridgeR3,axiom,
    ! [J: uni] : ( t2tb3(tb2t3(J)) = J ) ).

tff(min_def,axiom,
    ! [M: vertex1,Q: set_vertex,D: map_vertex_int] :
      ( min1(M,Q,D)
    <=> ( mem(vertex,t2tb2(M),t2tb(Q))
        & ! [X: vertex1] :
            ( mem(vertex,t2tb2(X),t2tb(Q))
           => $lesseq(tb2t3(get(int,vertex,t2tb1(D),t2tb2(M))),tb2t3(get(int,vertex,t2tb1(D),t2tb2(X)))) ) ) ) ).

tff(path,type,
    path1: ( vertex1 * vertex1 * $int ) > $o ).

tff(path_nil,axiom,
    ! [X: vertex1] : path1(X,X,0) ).

tff(path_cons,axiom,
    ! [X: vertex1,Y: vertex1,Z: vertex1,D: $int] :
      ( path1(X,Y,D)
     => ( mem(vertex,t2tb2(Z),t2tb(g_succ1(Y)))
       => path1(X,Z,$sum(D,weight1(Y,Z))) ) ) ).

tff(path_inversion,axiom,
    ! [Z: vertex1,Z1: vertex1,Z2: $int] :
      ( path1(Z,Z1,Z2)
     => ( ? [X: vertex1] :
            ( ( Z = X )
            & ( Z1 = X )
            & ( Z2 = 0 ) )
        | ? [X: vertex1,Y: vertex1,Z3: vertex1,D: $int] :
            ( path1(X,Y,D)
            & mem(vertex,t2tb2(Z3),t2tb(g_succ1(Y)))
            & ( Z = X )
            & ( Z1 = Z3 )
            & ( Z2 = $sum(D,weight1(Y,Z3)) ) ) ) ) ).

tff(length_nonneg,axiom,
    ! [X: vertex1,Y: vertex1,D: $int] :
      ( path1(X,Y,D)
     => $lesseq(0,D) ) ).

tff(shortest_path,type,
    shortest_path1: ( vertex1 * vertex1 * $int ) > $o ).

tff(shortest_path_def,axiom,
    ! [X: vertex1,Y: vertex1,D: $int] :
      ( shortest_path1(X,Y,D)
    <=> ( path1(X,Y,D)
        & ! [Dqt: $int] :
            ( path1(X,Y,Dqt)
           => $lesseq(D,Dqt) ) ) ) ).

tff(path_inversion1,axiom,
    ! [Src: vertex1,V: vertex1,D: $int] :
      ( path1(Src,V,D)
     => ( ( ( V = Src )
          & ( D = 0 ) )
        | ? [Vqt: vertex1] :
            ( path1(Src,Vqt,$difference(D,weight1(Vqt,V)))
            & mem(vertex,t2tb2(V),t2tb(g_succ1(Vqt))) ) ) ) ).

tff(path_shortest_path,axiom,
    ! [Src: vertex1,V: vertex1,D: $int] :
      ( path1(Src,V,D)
     => ? [Dqt: $int] :
          ( shortest_path1(Src,V,Dqt)
          & $lesseq(Dqt,D) ) ) ).

tff(main_lemma,axiom,
    ! [Src: vertex1,V: vertex1,D: $int] :
      ( path1(Src,V,D)
     => ( ~ shortest_path1(Src,V,D)
       => ( ( ( V = Src )
            & $less(0,D) )
          | ? [Vqt: vertex1,Dqt: $int] :
              ( shortest_path1(Src,Vqt,Dqt)
              & mem(vertex,t2tb2(V),t2tb(g_succ1(Vqt)))
              & $less($sum(Dqt,weight1(Vqt,V)),D) ) ) ) ) ).

tff(completeness_lemma,axiom,
    ! [S: set_vertex] :
      ( ! [V: vertex1] :
          ( mem(vertex,t2tb2(V),t2tb(S))
         => ! [W: vertex1] :
              ( mem(vertex,t2tb2(W),t2tb(g_succ1(V)))
             => mem(vertex,t2tb2(W),t2tb(S)) ) )
     => ! [Src: vertex1] :
          ( mem(vertex,t2tb2(Src),t2tb(S))
         => ! [Dst: vertex1,D: $int] :
              ( path1(Src,Dst,D)
             => mem(vertex,t2tb2(Dst),t2tb(S)) ) ) ) ).

tff(inv_src,type,
    inv_src1: ( vertex1 * set_vertex * set_vertex ) > $o ).

tff(inv_src_def,axiom,
    ! [Src: vertex1,S: set_vertex,Q: set_vertex] :
      ( inv_src1(Src,S,Q)
    <=> ( mem(vertex,t2tb2(Src),t2tb(S))
        | mem(vertex,t2tb2(Src),t2tb(Q)) ) ) ).

tff(inv,type,
    inv1: ( vertex1 * set_vertex * set_vertex * map_vertex_int ) > $o ).

tff(inv_def,axiom,
    ! [Src: vertex1,S: set_vertex,Q: set_vertex,D: map_vertex_int] :
      ( inv1(Src,S,Q,D)
    <=> ( inv_src1(Src,S,Q)
        & ( tb2t3(get(int,vertex,t2tb1(D),t2tb2(Src))) = 0 )
        & subset(vertex,t2tb(S),t2tb(v1))
        & subset(vertex,t2tb(Q),t2tb(v1))
        & ! [V: vertex1] :
            ( mem(vertex,t2tb2(V),t2tb(Q))
           => ( mem(vertex,t2tb2(V),t2tb(S))
             => $false ) )
        & ! [V: vertex1] :
            ( mem(vertex,t2tb2(V),t2tb(S))
           => shortest_path1(Src,V,tb2t3(get(int,vertex,t2tb1(D),t2tb2(V)))) )
        & ! [V: vertex1] :
            ( mem(vertex,t2tb2(V),t2tb(Q))
           => path1(Src,V,tb2t3(get(int,vertex,t2tb1(D),t2tb2(V)))) ) ) ) ).

tff(inv_succ,type,
    inv_succ1: ( vertex1 * set_vertex * set_vertex * map_vertex_int ) > $o ).

tff(inv_succ_def,axiom,
    ! [Src: vertex1,S: set_vertex,Q: set_vertex,D: map_vertex_int] :
      ( inv_succ1(Src,S,Q,D)
    <=> ! [X: vertex1] :
          ( mem(vertex,t2tb2(X),t2tb(S))
         => ! [Y: vertex1] :
              ( mem(vertex,t2tb2(Y),t2tb(g_succ1(X)))
             => ( ( mem(vertex,t2tb2(Y),t2tb(S))
                  | mem(vertex,t2tb2(Y),t2tb(Q)) )
                & $lesseq(tb2t3(get(int,vertex,t2tb1(D),t2tb2(Y))),$sum(tb2t3(get(int,vertex,t2tb1(D),t2tb2(X))),weight1(X,Y))) ) ) ) ) ).

tff(inv_succ2,type,
    inv_succ21: ( vertex1 * set_vertex * set_vertex * map_vertex_int * vertex1 * set_vertex ) > $o ).

tff(inv_succ2_def,axiom,
    ! [Src: vertex1,S: set_vertex,Q: set_vertex,D: map_vertex_int,U: vertex1,Su: set_vertex] :
      ( inv_succ21(Src,S,Q,D,U,Su)
    <=> ! [X: vertex1] :
          ( mem(vertex,t2tb2(X),t2tb(S))
         => ! [Y: vertex1] :
              ( mem(vertex,t2tb2(Y),t2tb(g_succ1(X)))
             => ( ( ( X != U )
                  | ( ( X = U )
                    & ~ mem(vertex,t2tb2(Y),t2tb(Su)) ) )
               => ( ( mem(vertex,t2tb2(Y),t2tb(S))
                    | mem(vertex,t2tb2(Y),t2tb(Q)) )
                  & $lesseq(tb2t3(get(int,vertex,t2tb1(D),t2tb2(Y))),$sum(tb2t3(get(int,vertex,t2tb1(D),t2tb2(X))),weight1(X,Y))) ) ) ) ) ) ).

tff(wP_parameter_shortest_path_code,conjecture,
    ! [Src: vertex1,Dst: vertex1,D: map_vertex_int] :
      ( ( mem(vertex,t2tb2(Src),t2tb(v1))
        & mem(vertex,t2tb2(Dst),t2tb(v1)) )
     => ! [Q: set_vertex,D1: map_vertex_int,Visited: set_vertex] :
          ( ( ! [X: vertex1] : ~ mem(vertex,t2tb2(X),t2tb(Visited))
            & ( Q = tb2t(add(vertex,t2tb2(Src),empty(vertex))) )
            & ( D1 = tb2t1(set1(int,vertex,t2tb1(D),t2tb2(Src),t2tb3(0))) ) )
         => ! [Q1: set_vertex,D2: map_vertex_int,Visited1: set_vertex] :
              ( ( inv_src1(Src,Visited1,Q1)
                & ( tb2t3(get(int,vertex,t2tb1(D2),t2tb2(Src))) = 0 )
                & subset(vertex,t2tb(Visited1),t2tb(v1))
                & subset(vertex,t2tb(Q1),t2tb(v1))
                & ! [V: vertex1] :
                    ( mem(vertex,t2tb2(V),t2tb(Q1))
                   => ( mem(vertex,t2tb2(V),t2tb(Visited1))
                     => $false ) )
                & ! [V: vertex1] :
                    ( mem(vertex,t2tb2(V),t2tb(Visited1))
                   => shortest_path1(Src,V,tb2t3(get(int,vertex,t2tb1(D2),t2tb2(V)))) )
                & ! [V: vertex1] :
                    ( mem(vertex,t2tb2(V),t2tb(Q1))
                   => path1(Src,V,tb2t3(get(int,vertex,t2tb1(D2),t2tb2(V)))) )
                & ! [X: vertex1] :
                    ( mem(vertex,t2tb2(X),t2tb(Visited1))
                   => ! [Y: vertex1] :
                        ( mem(vertex,t2tb2(Y),t2tb(g_succ1(X)))
                       => ( ( mem(vertex,t2tb2(Y),t2tb(Visited1))
                            | mem(vertex,t2tb2(Y),t2tb(Q1)) )
                          & $lesseq(tb2t3(get(int,vertex,t2tb1(D2),t2tb2(Y))),$sum(tb2t3(get(int,vertex,t2tb1(D2),t2tb2(X))),weight1(X,Y))) ) ) )
                & ! [M: vertex1] :
                    ( ( mem(vertex,t2tb2(M),t2tb(Q1))
                      & ! [X: vertex1] :
                          ( mem(vertex,t2tb2(X),t2tb(Q1))
                         => $lesseq(tb2t3(get(int,vertex,t2tb1(D2),t2tb2(M))),tb2t3(get(int,vertex,t2tb1(D2),t2tb2(X)))) ) )
                   => ! [X: vertex1,Dx: $int] :
                        ( path1(Src,X,Dx)
                       => ( $less(Dx,tb2t3(get(int,vertex,t2tb1(D2),t2tb2(M))))
                         => mem(vertex,t2tb2(X),t2tb(Visited1)) ) ) ) )
             => ! [O: bool1] :
                  ( ( ( O = true1 )
                  <=> ! [X: vertex1] : ~ mem(vertex,t2tb2(X),t2tb(Q1)) )
                 => ( ( O != true1 )
                   => ( ~ ! [X: vertex1] : ~ mem(vertex,t2tb2(X),t2tb(Q1))
                     => ! [Q2: set_vertex,U: vertex1] :
                          ( ( mem(vertex,t2tb2(U),t2tb(Q1))
                            & ! [X: vertex1] :
                                ( mem(vertex,t2tb2(X),t2tb(Q1))
                               => $lesseq(tb2t3(get(int,vertex,t2tb1(D2),t2tb2(U))),tb2t3(get(int,vertex,t2tb1(D2),t2tb2(X)))) )
                            & ( Q2 = tb2t(remove(vertex,t2tb2(U),t2tb(Q1))) ) )
                         => ( ( path1(Src,U,tb2t3(get(int,vertex,t2tb1(D2),t2tb2(U))))
                              & ! [Dqt: $int] :
                                  ( path1(Src,U,Dqt)
                                 => $lesseq(tb2t3(get(int,vertex,t2tb1(D2),t2tb2(U))),Dqt) ) )
                           => ! [Visited2: set_vertex] :
                                ( ( Visited2 = tb2t(add(vertex,t2tb2(U),t2tb(Visited1))) )
                               => ! [Su: set_vertex,Q3: set_vertex,D3: map_vertex_int] :
                                    ( ( ! [X: vertex1] :
                                          ( mem(vertex,t2tb2(X),t2tb(Su))
                                         => mem(vertex,t2tb2(X),t2tb(g_succ1(U))) )
                                      & inv_src1(Src,Visited2,Q3)
                                      & ( tb2t3(get(int,vertex,t2tb1(D3),t2tb2(Src))) = 0 )
                                      & subset(vertex,t2tb(Visited2),t2tb(v1))
                                      & subset(vertex,t2tb(Q3),t2tb(v1))
                                      & ! [V: vertex1] :
                                          ( mem(vertex,t2tb2(V),t2tb(Q3))
                                         => ( mem(vertex,t2tb2(V),t2tb(Visited2))
                                           => $false ) )
                                      & ! [V: vertex1] :
                                          ( mem(vertex,t2tb2(V),t2tb(Visited2))
                                         => shortest_path1(Src,V,tb2t3(get(int,vertex,t2tb1(D3),t2tb2(V)))) )
                                      & ! [V: vertex1] :
                                          ( mem(vertex,t2tb2(V),t2tb(Q3))
                                         => path1(Src,V,tb2t3(get(int,vertex,t2tb1(D3),t2tb2(V)))) )
                                      & ! [X: vertex1] :
                                          ( mem(vertex,t2tb2(X),t2tb(Visited2))
                                         => ! [Y: vertex1] :
                                              ( mem(vertex,t2tb2(Y),t2tb(g_succ1(X)))
                                             => ( ( ( X != U )
                                                  | ( ( X = U )
                                                    & ~ mem(vertex,t2tb2(Y),t2tb(Su)) ) )
                                               => ( ( mem(vertex,t2tb2(Y),t2tb(Visited2))
                                                    | mem(vertex,t2tb2(Y),t2tb(Q3)) )
                                                  & $lesseq(tb2t3(get(int,vertex,t2tb1(D3),t2tb2(Y))),$sum(tb2t3(get(int,vertex,t2tb1(D3),t2tb2(X))),weight1(X,Y))) ) ) ) ) )
                                   => ! [Result: bool1] :
                                        ( ( ( Result = true1 )
                                        <=> ~ ! [X: vertex1] : ~ mem(vertex,t2tb2(X),t2tb(Su)) )
                                       => ( ( Result = true1 )
                                         => ( ~ ! [X: vertex1] : ~ mem(vertex,t2tb2(X),t2tb(Su))
                                           => ! [Su1: set_vertex,V: vertex1] :
                                                ( ( mem(vertex,t2tb2(V),t2tb(Su))
                                                  & ( Su1 = tb2t(remove(vertex,t2tb2(V),t2tb(Su))) ) )
                                               => ! [Q4: set_vertex,D4: map_vertex_int] :
                                                    ( ( ( mem(vertex,t2tb2(V),t2tb(Visited2))
                                                        & ( Q4 = Q3 )
                                                        & ( D4 = D3 ) )
                                                      | ( mem(vertex,t2tb2(V),t2tb(Q4))
                                                        & $lesseq(tb2t3(get(int,vertex,t2tb1(D4),t2tb2(V))),$sum(tb2t3(get(int,vertex,t2tb1(D4),t2tb2(U))),weight1(U,V)))
                                                        & ( Q4 = Q3 )
                                                        & ( D4 = D3 ) )
                                                      | ( mem(vertex,t2tb2(V),t2tb(Q4))
                                                        & $less($sum(tb2t3(get(int,vertex,t2tb1(D3),t2tb2(U))),weight1(U,V)),tb2t3(get(int,vertex,t2tb1(D3),t2tb2(V))))
                                                        & ( Q4 = Q3 )
                                                        & ( D4 = tb2t1(set1(int,vertex,t2tb1(D3),t2tb2(V),t2tb3($sum(tb2t3(get(int,vertex,t2tb1(D3),t2tb2(U))),weight1(U,V))))) ) )
                                                      | ( ~ mem(vertex,t2tb2(V),t2tb(Visited2))
                                                        & ~ mem(vertex,t2tb2(V),t2tb(Q3))
                                                        & ( Q4 = tb2t(add(vertex,t2tb2(V),t2tb(Q3))) )
                                                        & ( D4 = tb2t1(set1(int,vertex,t2tb1(D3),t2tb2(V),t2tb3($sum(tb2t3(get(int,vertex,t2tb1(D3),t2tb2(U))),weight1(U,V))))) ) ) )
                                                   => ( ( $less(tb2t3(get(int,vertex,t2tb1(D4),t2tb2(V))),$sum(tb2t3(get(int,vertex,t2tb1(D4),t2tb2(U))),weight1(U,V)))
                                                        | ( tb2t3(get(int,vertex,t2tb1(D4),t2tb2(V))) = $sum(tb2t3(get(int,vertex,t2tb1(D4),t2tb2(U))),weight1(U,V)) ) )
                                                     => ! [X: vertex1] :
                                                          ( mem(vertex,t2tb2(X),t2tb(Visited2))
                                                         => ! [Y: vertex1] :
                                                              ( mem(vertex,t2tb2(Y),t2tb(g_succ1(X)))
                                                             => ( ( ( X != U )
                                                                  | ( ( X = U )
                                                                    & ~ mem(vertex,t2tb2(Y),t2tb(Su1)) ) )
                                                               => ( mem(vertex,t2tb2(Y),t2tb(Visited2))
                                                                  | mem(vertex,t2tb2(Y),t2tb(Q4)) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ).

%------------------------------------------------------------------------------

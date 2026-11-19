% $o has exactly two elements, whatever fmb_start_size says.
%
% FMB used to bound $o only as the EPR rule bounds any sort without functions: by its number
% of constants, which includes FOOL elimination's names for the formulas in term position
% here (the p(_, p(_,_)) nestings). With -fmbss 3 it therefore started $o at 3 elements, and
% the size search, which needs $i to grow to 5 for f's 5-cycles, went on from there: at [5,3]
% it found a "model" with three booleans that the model printing rejects (a debug build
% asserts size == 2, a release one reads past the two boolean element names). Now $o is pinned
% to 2, and a start size above a detected maximum starts that sort at the maximum instead.

tff(e_type,type,e: $i).
tff(f_type,type,f: $i > $i).
tff(p_type,type,p: ( $i * $o ) > $o).
tff(q_type,type,q: $o).
tff(r_type,type,r: $o).
tff(s_type,type,s: $o).

tff(no_short_cycles,axiom,
    ! [X: $i] : ( f(X) != X & f(f(X)) != X & f(f(f(X))) != X & f(f(f(f(X)))) != X ) ).
tff(f_injective,axiom,
    ! [X: $i,Y: $i] : ( f(X) = f(Y) => X = Y ) ).
tff(p_either,axiom,
    ! [X: $i] : ( p(X,q) <~> p(X,$true) ) ).
tff(nested,axiom,
    ( p(e,p(f(e),q)) & p(f(e),p(e,~r)) & ( s <=> p(e,r) ) ) ).

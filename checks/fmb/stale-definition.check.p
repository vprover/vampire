% The model -fmbmp layered prints for fmb/stale-definition.p under -pel on, read back: r and s
% are defined over the earlier version 'x_$1' of x, which is declared and defined like any
% other symbol.
%
% A definition that is stale by the time the model is printed: it reads a symbol that changes
% after it, so it must be printed over that symbol's earlier version, not its final one.
%
% Unused predicate definition removal sees x used only positively, so it keeps only
% x => (r & s) and records a flip of x, to be replayed at the end. Predicate elimination,
% which runs later in preprocessing, then eliminates r and s, whose definitions mention x,
% and x itself. Replayed backwards, the definitions of r and s come before x's flip and read
% x as it was before it. So -fmbmp layered prints them over 'x_$1' (x before its last
% update, itself a definition), and x, a flip on top, as a table. Before versions existed,
% r and s were spelled out as tables.
%
% x has three positive uses so that eliminating it first would cost more clauses than it
% removes; otherwise predicate elimination takes x before r and s, and nothing goes stale.

fof(def_x, axiom, ! [X] : ( x(X) <=> ( r(X) & s(X) ) )).
fof(u1, axiom, x(a)).
fof(u2, axiom, x(c)).
fof(u3, axiom, x(d)).
fof(o1, axiom, ~ r(b)).
fof(o2, axiom, ~ s(e)).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2'
).

tff(declare_a,type,a : $i).
tff(declare_c,type,c : $i).
tff(declare_d,type,d : $i).
tff(declare_b,type,b : $i).
tff(declare_e,type,e : $i).
tff(declare_x,type,x: ( $i ) > $o ).
tff(declare_r,type,r: ( $i ) > $o ).
tff(declare_s,type,s: ( $i ) > $o ).
tff('declare_x_$1',type,'x_$1': ( $i ) > $o ).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(c_definition,axiom,c = 'fmb_$i_1').
tff(d_definition,axiom,d = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(e_definition,axiom,e = 'fmb_$i_2').
tff(predicate_x,axiom,
           x('fmb_$i_1')
         & ~x('fmb_$i_2')
).

tff(r_symbolic_definition,axiom,![X0:$i]: (r(X0) <=> (? [X1:$i] : ('x_$1'(X1) & (X0 = X1))))).
tff(s_symbolic_definition,axiom,![X0:$i]: (s(X0) <=> (? [X1:$i] : ('x_$1'(X1) & (X0 = X1))))).
tff('x_$1_symbolic_definition',axiom,![X0:$i]: ('x_$1'(X0) <=> ((d = X0) | (c = X0) | (a = X0)))).
vampire(model_check,model_end).

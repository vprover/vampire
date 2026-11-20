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
% update, itself a definition), and x, a flip on top, as a $cond over 'x_$1' too. Before
% versions existed, r and s were spelled out as tables.
%
% x has three positive uses so that eliminating it first would cost more clauses than it
% removes; otherwise predicate elimination takes x before r and s, and nothing goes stale.
% And r and s hold of an f that x's own definition does not make true, so that the flip,
% which makes x true wherever r & s does, changes x there: a flip that changes nothing is not
% kept, and then r and s would read the final x after all.

fof(def_x, axiom, ! [X] : ( x(X) <=> ( r(X) & s(X) ) )).
fof(u1, axiom, x(a)).
fof(u2, axiom, x(c)).
fof(u3, axiom, x(d)).
fof(o1, axiom, ~ r(b)).
fof(o2, axiom, ~ s(e)).
fof(f1, axiom, r(f) & s(f)).
fof(f2, axiom, f != a).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('declare_$i3',type,'fmb_$i_3':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2') | (X = 'fmb_$i_3')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2' & 'fmb_$i_1' != 'fmb_$i_3' & 'fmb_$i_2' != 'fmb_$i_3'
).

tff(declare_a,type,a : $i).
tff(declare_c,type,c : $i).
tff(declare_d,type,d : $i).
tff(declare_b,type,b : $i).
tff(declare_e,type,e : $i).
tff(declare_f,type,f : $i).
tff(declare_x,type,x: ( $i ) > $o ).
tff(declare_r,type,r: ( $i ) > $o ).
tff(declare_s,type,s: ( $i ) > $o ).
tff('declare_x_$1',type,'x_$1': ( $i ) > $o ).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(c_definition,axiom,c = 'fmb_$i_1').
tff(d_definition,axiom,d = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_3').
tff(e_definition,axiom,e = 'fmb_$i_3').
tff(f_definition,axiom,f = 'fmb_$i_2').
tff(x_symbolic_definition,axiom,![X0:$i]: (x(X0) <=> $cond(
           ((X0 = 'fmb_$i_2')), $true,
           'x_$1'(X0)))).
tff(r_symbolic_definition,axiom,![X0:$i]: (r(X0) <=> ((? [X1:$i] : ('x_$1'(X1) & (X0 = X1))) | (f = X0)))).
tff(s_symbolic_definition,axiom,![X0:$i]: (s(X0) <=> ((f = X0) | (? [X1:$i] : ('x_$1'(X1) & (X0 = X1)))))).
tff('x_$1_symbolic_definition',axiom,![X0:$i]: ('x_$1'(X0) <=> ((a = X0) | (c = X0) | (d = X0)))).
vampire(model_check,model_end).

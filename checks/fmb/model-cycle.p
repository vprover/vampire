% model_check must reject definitions that depend on each other in a cycle, here of
% length three; the message names the whole cycle.

tff(f_type,type,f: $i > $i).
tff(g_type,type,g: $i > $i).
tff(h_type,type,h: $i > $i).
tff(p_type,type,p: $i > $o).

tff(goal,axiom, ! [X: $i] : f(X) = X ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('finite_domain_$i',axiom, ! [X:$i] : ( (X = 'fmb_$i_1') | (X = 'fmb_$i_2') ) ).
tff('distinct_domain_$i',axiom, 'fmb_$i_1' != 'fmb_$i_2' ).
tff(function_h,axiom, h('fmb_$i_1') = 'fmb_$i_1' & h('fmb_$i_2') = 'fmb_$i_2' ).
tff(f_symbolic_definition,axiom,![X0:$i]: f(X0) = g(X0)).
tff(g_symbolic_definition,axiom,![X0:$i]: g(X0) = h2(X0)).
tff(h2_type,type,h2: $i > $i).
tff(h2_symbolic_definition,axiom,![X0:$i]: h2(X0) = f(X0)).
vampire(model_check,model_end).

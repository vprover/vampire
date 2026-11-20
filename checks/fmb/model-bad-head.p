% model_check must reject a symbolic definition whose head arguments are not pairwise
% distinct variables.

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
tff(k_type,type,k: ($i * $i) > $i).
tff(k_symbolic_definition,axiom,![X0:$i]: k(X0,X0) = 'fmb_$i_1').
tff(f_symbolic_definition,axiom,![X0:$i]: f(X0) = h(X0)).
vampire(model_check,model_end).

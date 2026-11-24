% model_check must reject, at load time, a definition whose body mentions a symbol the
% model says nothing about -- even though here no formula to check would ever need it.

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
tff(f_symbolic_definition,axiom,![X0:$i]: f(X0) = $ite(p(X0), g(X0), X0)).
vampire(model_check,model_end).

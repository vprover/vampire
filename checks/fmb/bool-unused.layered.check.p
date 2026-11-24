include('fmb/bool-unused.p').
vampire(model_check,model_start).
tff(finite_domain_bool,axiom,
      ! [X:$o] : (
         (X = $false) | (X = $true)
      ) ).

tff(distinct_domain_bool,axiom,
         $false != $true
).

tff(declare_a,type,a: $o ).
tff(declare_b,type,b: $o ).
tff(declare_p,type,p: ( $o ) > $o ).

tff(a_definition,axiom,~a).
tff(b_definition,axiom,~b).
tff(p_symbolic_definition,axiom,![X0:$o]: (p(X0) <=> $false)).
vampire(model_check,model_end).

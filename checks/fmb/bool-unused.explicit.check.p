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
tff(a_definition,axiom,~a).
tff(declare_b,type,b: $o ).
tff(b_definition,axiom,~b).
tff(declare_p,type,p: ( $o ) > $o ).
tff(predicate_p,axiom,
           ~p($false)
         & ~p($true)
).

vampire(model_check,model_end).

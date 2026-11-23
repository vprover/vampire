include('fmb/bool-replay.p').
vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1')
      ) ).

tff(finite_domain_bool,axiom,
      ! [X:$o] : (
         (X = $false) | (X = $true)
      ) ).

tff(distinct_domain_bool,axiom,
         $false != $true
).

tff(declare_emptyset,type,emptyset : $i).
tff(declare_in,type,in: ( $i * $i ) > $o ).
tff(declare_emptysetE,type,emptysetE: $o ).

tff(emptyset_definition,axiom,emptyset = 'fmb_$i_1').
tff(in_symbolic_definition,axiom,![X0:$i, X1:$i]: (in(X0,X1) <=> $true)).
tff(emptysetE_symbolic_definition,axiom,emptysetE <=> (! [X0:$i] : (in(X0,emptyset) => (! [X1:$o] : ($true = X1))))).
vampire(model_check,model_end).

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
tff(emptyset_definition,axiom,emptyset = 'fmb_$i_1').
tff(declare_in,type,in: ( $i * $i ) > $o ).
tff(predicate_in,axiom,
           in('fmb_$i_1','fmb_$i_1')
).

tff(declare_emptysetE,type,emptysetE: $o ).
tff(emptysetE_definition,axiom,~emptysetE).
vampire(model_check,model_end).

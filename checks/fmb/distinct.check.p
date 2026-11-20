% The model FMB prints for fmb/distinct.p, read back: model_check evaluates the problem's
% $distinct markers with the same evaluator as the FMB self-check.

tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(c_type,type,c: $i).
tff(d_type,type,d: $i).
tff(e_type,type,e: $i).
tff(p_type,type,p: $i > $o).
tff(abcd,axiom, $distinct(a,b,c,d) ).
tff(not_all_distinct,axiom, ~ $distinct(a,b,c,d,e) ).
tff(p_a,axiom, p(a) & ~ p(b) ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('declare_$i3',type,'fmb_$i_3':$i).
tff('declare_$i4',type,'fmb_$i_4':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2') | (X = 'fmb_$i_3') | (X = 'fmb_$i_4')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2' & 'fmb_$i_1' != 'fmb_$i_3' & 'fmb_$i_1' != 'fmb_$i_4' & 'fmb_$i_2' != 'fmb_$i_3' & 'fmb_$i_2' != 'fmb_$i_4' & 
         'fmb_$i_3' != 'fmb_$i_4'
).

tff(declare_a,type,a : $i).
tff(a_definition,axiom,a = 'fmb_$i_1').
tff(declare_b,type,b : $i).
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(declare_c,type,c : $i).
tff(c_definition,axiom,c = 'fmb_$i_3').
tff(declare_d,type,d : $i).
tff(d_definition,axiom,d = 'fmb_$i_4').
tff(declare_e,type,e : $i).
tff(e_definition,axiom,e = 'fmb_$i_1').
tff(declare_p,type,p: ( $i ) > $o ).
tff(predicate_p,axiom,
           p('fmb_$i_1')
         & ~p('fmb_$i_2')
         & ~p('fmb_$i_3')
         & ~p('fmb_$i_4')
).

vampire(model_check,model_end).

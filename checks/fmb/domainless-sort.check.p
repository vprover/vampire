% The model FMB prints for fmb/domainless-sort.p, read back: s has to come with a domain,
% the singleton, for the loader to know what fmb_s_1 is and for f, g, k and p to be
% interpreted at all.

tff(s_type,type,s: $tType).
tff(t_type,type,t: $tType).
tff(f_type,type,f: s > t).
tff(g_type,type,g: t > s).
tff(k_type,type,k: s).
tff(p_type,type,p: s > $o).
tff(c_type,type,c: t).
tff(d_type,type,d: t).
tff(cd,axiom, c != d).

vampire(model_check,model_start).
tff(declare_s,type,s:$tType).
tff(declare_s1,type,fmb_s_1:s).
tff(finite_domain_s,axiom,
      ! [X:s] : (
         (X = fmb_s_1)
      ) ).

tff(declare_t,type,t:$tType).
tff(declare_t1,type,fmb_t_1:t).
tff(declare_t2,type,fmb_t_2:t).
tff(finite_domain_t,axiom,
      ! [X:t] : (
         (X = fmb_t_1) | (X = fmb_t_2)
      ) ).

tff(distinct_domain_t,axiom,
         fmb_t_1 != fmb_t_2
).

tff(declare_f,type,f : ( s ) > t).
tff(function_f,axiom,
           f(fmb_s_1) = fmb_t_1
).

tff(declare_g,type,g : ( t ) > s).
tff(function_g,axiom,
           g(fmb_t_1) = fmb_s_1
         & g(fmb_t_2) = fmb_s_1
).

tff(declare_k,type,k : s).
tff(k_definition,axiom,k = fmb_s_1).
tff(declare_c,type,c : t).
tff(c_definition,axiom,c = fmb_t_1).
tff(declare_d,type,d : t).
tff(d_definition,axiom,d = fmb_t_2).
tff(declare_p,type,p: ( s ) > $o ).
tff(predicate_p,axiom,
           ~p(fmb_s_1)
).

vampire(model_check,model_end).

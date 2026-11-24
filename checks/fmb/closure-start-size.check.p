% The model FMB prints for fmb/closure-start-size.p under -fmbss 4, read back: this is what checks the model
% now that the in-run self-check (FMB_CHECK_MODEL_AGAINST_INPUT) is off.
%
% A sort bounded by a domain-closure axiom, with more constants than the axiom names.
%
% only_abc bounds k to 3 elements (sort inference's { X = t_i } bound, which caps the grounding
% of every k variable at 3). The skolem for some_p is a fourth constant of k, and nothing maps
% into k, so the EPR rule bounded k by its 4 constants -- and used to *raise* the maximum to
% that, rather than keep the tighter 3. With -fmbss 4 FMB then searched at size 4, where
% only_abc is grounded over elements 1..3 alone and the constants' values are capped at 3 too:
% element 4 occurred in no clause, and the model found was reported with a fourth k that none
% of a, b, c denotes. The FMB model self-check rejected it. Now the maximum stays 3, and the
% start size is clamped to it.
%
% Found on Problems/PUZ/PUZ134_20.p with --decode fmb+10_1_fmbss=10_60.

tff(k_type,type,k: $tType).
tff(a_type,type,a: k).
tff(b_type,type,b: k).
tff(c_type,type,c: k).
tff(p_type,type,p: k > $o).

tff(abc_distinct,axiom, ( a != b & a != c & b != c ) ).
tff(only_abc,axiom, ! [X: k] : ( X = a | X = b | X = c ) ).
tff(some_p,axiom, ? [X: k] : p(X) ).
tff(not_p_a,axiom, ~ p(a) ).

vampire(model_check,model_start).
tff(declare_k,type,k:$tType).
tff(declare_k1,type,fmb_k_1:k).
tff(declare_k2,type,fmb_k_2:k).
tff(declare_k3,type,fmb_k_3:k).
tff(finite_domain_k,axiom,
      ! [X:k] : (
         (X = fmb_k_1) | (X = fmb_k_2) | (X = fmb_k_3)
      ) ).

tff(distinct_domain_k,axiom,
         fmb_k_1 != fmb_k_2 & fmb_k_1 != fmb_k_3 & fmb_k_2 != fmb_k_3
).

tff(declare_a,type,a : k).
tff(a_definition,axiom,a = fmb_k_1).
tff(declare_b,type,b : k).
tff(b_definition,axiom,b = fmb_k_2).
tff(declare_c,type,c : k).
tff(c_definition,axiom,c = fmb_k_3).
tff(declare_p,type,p: ( k ) > $o ).
tff(predicate_p,axiom,
           ~p(fmb_k_1)
         & p(fmb_k_2)
         & p(fmb_k_3)
).

vampire(model_check,model_end).

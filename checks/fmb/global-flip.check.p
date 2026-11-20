% The model -fmbmp layered prints for fmb/global-flip.p under --random_polarities on
% --random_seed 2, read back: p and q are negations of their earlier versions.
%
% Global flips, as -rp on (random_polarities) makes them: preprocessing swaps the polarity of
% some predicates throughout, and the model reconstruction swaps them back. -fmbmp layered
% prints such a predicate as the negation of its version below the flip,
% ![X0:$i]: (p(X0) <=> ~'p_$1'(X0)), 'p_$1' being the table FMB found; before, it was
% spelled out as a table of the flipped values. Which predicates get flipped depends on the
% random seed, so the check fixes it. (Both predicates occur in both polarities, or pure
% predicate removal would define them away before any flip.)

fof(ab, axiom, p(a) & ~ p(b) ).
fof(pq, axiom, ! [X] : ( p(X) | q(X) ) ).
fof(qp, axiom, ! [X] : ( ~ q(X) | ~ p(X) ) ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1') | (X = 'fmb_$i_2')
      ) ).

tff('distinct_domain_$i',axiom,
         'fmb_$i_1' != 'fmb_$i_2'
).

tff(declare_a,type,a : $i).
tff(declare_b,type,b : $i).
tff(declare_p,type,p: ( $i ) > $o ).
tff(declare_q,type,q: ( $i ) > $o ).
tff('declare_p_$1',type,'p_$1': ( $i ) > $o ).
tff('declare_q_$1',type,'q_$1': ( $i ) > $o ).

tff(a_definition,axiom,a = 'fmb_$i_1').
tff(b_definition,axiom,b = 'fmb_$i_2').
tff(p_symbolic_definition,axiom,![X0:$i]: (p(X0) <=> ~'p_$1'(X0))).
tff(q_symbolic_definition,axiom,![X0:$i]: (q(X0) <=> ~'q_$1'(X0))).
tff('predicate_p_$1',axiom,
           ~'p_$1'('fmb_$i_1')
         & 'p_$1'('fmb_$i_2')
).

tff('predicate_q_$1',axiom,
           'q_$1'('fmb_$i_1')
         & ~'q_$1'('fmb_$i_2')
).

vampire(model_check,model_end).

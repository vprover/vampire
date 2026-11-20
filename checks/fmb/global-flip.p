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

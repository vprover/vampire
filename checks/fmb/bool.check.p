% The model checks/fmb/bool.out prints, fed back in: a printed model must be re-readable,
% which for $o means the parser has to see through $true / $false in term position.
% Regenerate with: vampire -sa fmb --statistics none fmb/bool.p (model part only).

% FMB over a problem that uses $o as an ordinary sort (the FOOL fragment consisting of
% $true and $false at term level). FOOLElimination compiles the booleans into ordinary
% terms and TheoryAxioms::applyFOOL pins their domain to two elements, so FMB models $o
% like any other sort; the model prints its two elements as $true and $false.
%
% f exercises $o as a result sort (the parser turns such a declaration into a predicate),
% g exercises it as an argument sort, and both keep it alive through preprocessing.

tff(t1, type, f: $i > $o).
tff(t2, type, g: ($o * $i) > $i).
tff(t3, type, a: $i).

tff(ax1, axiom, f(a) = $true).
tff(ax2, axiom, ?[Y:$i]: f(Y) = $false).
tff(ax3, axiom, ![B:$o, X:$i]: f(g(B,X)) = B).
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

tff(finite_domain_bool,axiom,
      ! [X:$o] : (
         (X = $false) | (X = $true)
      ) ).

tff(distinct_domain_bool,axiom,
         $false != $true
).

tff(declare_g,type,g : ( $o * $i ) > $i).
tff(function_g,axiom,
           g($false,'fmb_$i_1') = 'fmb_$i_2'
         & g($true,'fmb_$i_1') = 'fmb_$i_1'
         & g($false,'fmb_$i_2') = 'fmb_$i_2'
         & g($true,'fmb_$i_2') = 'fmb_$i_1'
).

tff(declare_a,type,a : $i).
tff(a_definition,axiom,a = 'fmb_$i_1').
tff(declare_f,type,f: ( $i ) > $o ).
tff(predicate_f,axiom,
           f('fmb_$i_1')
         & ~f('fmb_$i_2')
).

vampire(model_check,model_end).

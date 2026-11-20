% model_check loads a predicate definition of the shape FMB prints a conditional flip in,
% p(Xs) <=> $cond(((X0 = e) & ...), $true or $false, ..., else), as the flip it was printed
% from: a definition p := else with a layer of the cases on top, so that a lookup is a hash
% probe rather than a walk through the cases. Any other $cond stays an ordinary definition.
%
% q is of the shape, with the tuple of 'fmb_$i_1' given twice: as in $cond, the first case
% must win, so q('fmb_$i_1') is true. r is not of the shape (its condition is not about the
% arguments alone), so it is evaluated as written. Both must make the formulas below true.

tff(p_type,type,p: $i > $o).
tff(q_type,type,q: $i > $o).
tff(r_type,type,r: $i > $o).

tff(first_case_wins,axiom, q('fmb_$i_1') ).
tff(falls_back,axiom, q('fmb_$i_2') ).
tff(general,axiom, ! [X: $i] : ( r(X) <=> ~ p(X) ) ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('declare_$i2',type,'fmb_$i_2':$i).
tff('finite_domain_$i',axiom, ! [X:$i] : ( (X = 'fmb_$i_1') | (X = 'fmb_$i_2') ) ).
tff('distinct_domain_$i',axiom, 'fmb_$i_1' != 'fmb_$i_2' ).
tff(predicate_p,axiom, ~ p('fmb_$i_1') & p('fmb_$i_2') ).
tff(q_symbolic_definition,axiom,![X0:$i]: (q(X0) <=> $cond(
           ((X0 = 'fmb_$i_1')), $true,
           ((X0 = 'fmb_$i_1')), $false,
           p(X0)))).
tff(r_symbolic_definition,axiom,![X0:$i]: (r(X0) <=> $cond(
           p(X0), $false,
           $true))).
vampire(model_check,model_end).

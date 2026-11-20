% The model -fmbmp layered prints for fmb/no-clauses.p, a problem preprocessing leaves without
% a single clause, read back.
%
% Preprocessing leaves no clauses at all: p is defined but never used, so its definition goes
% (unused predicate definition removal), and t and n each occur in one polarity only, so
% pure predicate removal takes the rest. FMB used to answer Satisfiable straight away, with no
% model; it now runs as on any other problem -- there are no sorts to size ("TRYING []"), the
% SAT problem is empty -- and prints the model the replay of what preprocessing recorded
% makes, which the self-check confirms. (Problems/KRS/KRS025+1.p, in small.)

fof(def_p, axiom, ! [X] : ( p(X) <=> ( t(X) & ~ n(X) ) )).
fof(pure, axiom, ! [X] : ( t(X) & ~ n(X) ) ).
fof(fact, axiom, t(c) ).

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1')
      ) ).

tff(declare_c,type,c : $i).
tff(declare_p,type,p: ( $i ) > $o ).
tff(declare_t,type,t: ( $i ) > $o ).
tff(declare_n,type,n: ( $i ) > $o ).

tff(c_definition,axiom,c = 'fmb_$i_1').
tff(p_symbolic_definition,axiom,![X0:$i]: (p(X0) <=> (~n(X0) & t(X0)))).
tff(t_symbolic_definition,axiom,![X0:$i]: (t(X0) <=> $true)).
tff(n_symbolic_definition,axiom,![X0:$i]: (n(X0) <=> $false)).
vampire(model_check,model_end).

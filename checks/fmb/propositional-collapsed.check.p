% The model FMB prints for fmb/propositional-collapsed.p under -fmbas predicate, read back.
% It is purely propositional, so it has no finite_domain axiom at all; model_check used to
% refuse it for that alone.
%
% A propositional problem under -fmbas predicate (or function).
%
% With no non-ground clauses FMB skips sort inference, and under -fmbas predicate / function
% that path creates the one collapsed distinct sort up front, before it is known whether any
% sort is used. Here none is, so the position stands for no vampire sort, and the
% "% Sorts in the size vectors:" line, which assumed every position names at least one,
% failed an assertion (and read past an empty stack in a release build). It now prints [{}].
%
% Found on Problems/SYN/SYN092-1.003.p with
% --decode fmb+10_1_fmbas=predicate:rpr=on:si=on_10, where the randomized preprocessing
% happens to leave only ground clauses.

cnf(c1,axiom, ( p | q ) ).
cnf(c2,axiom, ( ~ p | ~ q ) ).
cnf(c3,axiom, ( p | r ) ).
cnf(c4,axiom, ( ~ r | q | s ) ).
cnf(c5,axiom, ( ~ s | ~ p ) ).

vampire(model_check,model_start).
tff(declare_p,type,p: $o ).
tff(p_definition,axiom,p).
tff(declare_q,type,q: $o ).
tff(q_definition,axiom,~q).
tff(declare_r,type,r: $o ).
tff(r_definition,axiom,~r).
tff(declare_s,type,s: $o ).
tff(s_definition,axiom,~s).
vampire(model_check,model_end).

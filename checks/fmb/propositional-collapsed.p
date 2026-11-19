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

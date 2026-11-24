% Preprocessing leaves no clauses at all: p is defined but never used, so its definition goes
% (unused predicate definition removal), and t and n each occur in one polarity only, so
% pure predicate removal takes the rest. FMB used to answer Satisfiable straight away, with no
% model; it now runs as on any other problem -- there are no sorts to size ("TRYING []"), the
% SAT problem is empty -- and prints the model the replay of what preprocessing recorded
% makes, which the self-check confirms. (Problems/KRS/KRS025+1.p, in small.)

fof(def_p, axiom, ! [X] : ( p(X) <=> ( t(X) & ~ n(X) ) )).
fof(pure, axiom, ! [X] : ( t(X) & ~ n(X) ) ).
fof(fact, axiom, t(c) ).

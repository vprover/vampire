% w occurs only positively outside its definition, so unused predicate definition removal
% weakens the definition to w(Xs) => (q(X0) | q(X7)) and records a conditional flip to
% restore it. Replaying that flip used to enumerate all 41^8 argument tuples of w (and
% remember a value for each), running out of memory, as in MGT095+1 under -fmbss 41;
% now the flip is a definition over the version of w below it, evaluated on demand
% (FiniteModelMultiSorted::condFlipAsDefinition).
tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(q_type,type,q: $i > $o).
tff(w_type,type,w: ($i * $i * $i * $i * $i * $i * $i * $i) > $o).
tff(def,axiom, ! [X0:$i,X1:$i,X2:$i,X3:$i,X4:$i,X5:$i,X6:$i,X7:$i] :
    ( w(X0,X1,X2,X3,X4,X5,X6,X7) <=> ( q(X0) | q(X7) ) ) ).
tff(use,axiom, w(a,b,a,b,a,b,a,b) ).
tff(qa,axiom, ~q(a) ).
tff(qb,axiom, q(b) ).
% a function, so that the domain is not bounded by the constants and -fmbss 41 applies
tff(f_type,type,f: $i > $i).
tff(fx,axiom, ! [X:$i] : f(X) != X ).

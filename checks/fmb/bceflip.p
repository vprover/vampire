% A predicate that blocked clause elimination makes disappear *entirely*: all three
% clauses of complement(X,Y) <=> (meet(X,Y) = n0 & join(X,Y) = n1) are blocked, so
% complement's usageCnt drops to zero -- the finite model gets no table for it, and BCE
% records no definition for it either, only three conditional flips. Those flips are then
% the only thing the model ever learns about complement, and unlike a definition they
% prescribe its value just on the arguments their condition selects, leaving it alone
% everywhere else. A replay that skips a flip whose target the model does not represent yet
% leaves complement trivially false and violates meet_join_complement.
%
% The lattice axioms are here only to keep the clause set non-empty after elimination, so
% that finite model building actually runs.
cnf(idempotence_of_meet,axiom,
    meet(X,X) = X ).

cnf(absorption1,axiom,
    meet(X,join(X,Y)) = X ).

cnf(absorption2,axiom,
    join(X,meet(X,Y)) = X ).

cnf(commutativity_of_meet,axiom,
    meet(X,Y) = meet(Y,X) ).

cnf(complement_meet,axiom,
    ( ~ complement(X,Y)
    | meet(X,Y) = n0 ) ).

cnf(complement_join,axiom,
    ( ~ complement(X,Y)
    | join(X,Y) = n1 ) ).

cnf(meet_join_complement,axiom,
    ( meet(X,Y) != n0
    | join(X,Y) != n1
    | complement(X,Y) ) ).

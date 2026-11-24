% The model FMB prints for fmb/bceflip.p under -bce on, read back: this is what checks the model
% now that the in-run self-check (FMB_CHECK_MODEL_AGAINST_INPUT) is off.
%
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

vampire(model_check,model_start).
tff('declare_$i1',type,'fmb_$i_1':$i).
tff('finite_domain_$i',axiom,
      ! [X:$i] : (
         (X = 'fmb_$i_1')
      ) ).

tff(declare_meet,type,meet : ( $i * $i ) > $i).
tff(function_meet,axiom,
           meet('fmb_$i_1','fmb_$i_1') = 'fmb_$i_1'
).

tff(declare_join,type,join : ( $i * $i ) > $i).
tff(function_join,axiom,
           join('fmb_$i_1','fmb_$i_1') = 'fmb_$i_1'
).

tff(declare_n0,type,n0 : $i).
tff(n0_definition,axiom,n0 = 'fmb_$i_1').
tff(declare_n1,type,n1 : $i).
tff(n1_definition,axiom,n1 = 'fmb_$i_1').
tff(declare_complement,type,complement: ( $i * $i ) > $o ).
tff(predicate_complement,axiom,
           complement('fmb_$i_1','fmb_$i_1')
).

vampire(model_check,model_end).

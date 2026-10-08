% This refutation uses AVATAR, whose printed split prefix is represented by an
% internal function symbol carrying a nullary predicate type.  Proof printing
% must not treat that type's empty result marker as a tuple sort.
tff(type_s_a0, type, s_a0: $tType).
tff(type_t_a0, type, t_a0: (s_a0 > $o)).
tff(type_t_a1, type, t_a1: s_a0).
tff(type_t_a2, type, t_a2: $o).
tff(type_t_a3, type, t_a3: (s_a0 > $o)).
tff(type_t_a4, type, t_a4: (s_a0 > $o)).
tff(fact0, axiom, (~ (t_a0(t_a1) | (t_a2 | t_a3(t_a1))))).
tff(fact1, axiom, (! [X0: s_a0] : (t_a4(X0) | t_a0(X0)))).
tff(fact2, axiom, (! [X0: s_a0] : ((~ t_a4(X0)) | (t_a2 | t_a3(X0))))).

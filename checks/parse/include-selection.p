% Parser regression test (include() formula selection): integer names used to
% be rejected in the selection list, although TPTP has
% name ::= atomic_word | integer. Expected: units 27 and named are included.
include('include-selection-axioms.p', [27, named]).
fof(local, axiom, local_axiom).

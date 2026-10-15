% Parser regression test (THF binder bodies): a binder body is a
% <thf_unit_formula>, which includes equalities; the binder used to close over
% just the first unitary item, reading a1's lambda as (^[T]: T) = e_b (a sort
% error) and failing on a2 with "Non-boolean term".
% Expected: the equalities belong inside the binders.
thf(t1, type, tree_b: $tType).
thf(t2, type, e_b: tree_b).
thf(t3, type, heapIm229596387mpty_b: tree_b > $o).
thf(fact_0_hs__is__empty__def, axiom,
    ( heapIm229596387mpty_b
    = ( ^ [T: tree_b] : T = e_b ) ) ).
thf(bool_quant, axiom, ! [X: $o] : X = X).

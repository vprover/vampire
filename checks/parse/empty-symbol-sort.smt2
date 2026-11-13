; expected: Unsatisfiable; || is a valid quoted SMT-LIB symbol.
(declare-sort || 0)
(declare-fun a () ||)
(assert (= a a))
(assert (not (= a a)))
(check-sat)

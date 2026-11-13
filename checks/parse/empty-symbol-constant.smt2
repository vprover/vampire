; expected: Unsatisfiable; || is a valid quoted SMT-LIB symbol.
(declare-sort U 0)
(declare-fun a () U)
(declare-fun || () U)
(assert (= || a))
(assert (not (= || a)))
(check-sat)

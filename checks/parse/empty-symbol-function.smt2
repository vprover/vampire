; expected: Unsatisfiable; || is a valid quoted SMT-LIB symbol.
(declare-sort U 0)
(declare-fun a () U)
(declare-fun || (U) U)
(assert (= (|| a) a))
(assert (not (= (|| a) a)))
(check-sat)

; expected: Unsatisfiable; match on a parametric datatype still reduces.
(declare-datatypes ((Box 1)) ((par (T) ((box (value T))))))
(assert (not (match (box 1) (((box x) (= x 1))))))
(check-sat)

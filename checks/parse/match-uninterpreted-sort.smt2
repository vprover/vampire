; expected: reject a match scrutinee that is not a datatype.
(declare-sort U 0)
(declare-fun a () U)
(assert (match a ((x true))))

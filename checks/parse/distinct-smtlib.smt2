; SMT-LIB's distinct now goes through the same marker as TPTP's $distinct, so the
; quadratic expansion is no longer paid at parse time. Its arguments may be
; arbitrary terms, so only some occurrences can become a distinct group.
(set-logic UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(declare-fun x () U)
(assert (distinct a b c))
(assert (distinct (f x) (f a) (f b)))
(assert (= a b))
(check-sat)

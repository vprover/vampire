(set-logic UF)
(declare-sort s 0)
(declare-fun a () s)
(declare-fun b () s)
(assert (! (= a b) :named one))
(assert (! (not (= a b)) :named two))



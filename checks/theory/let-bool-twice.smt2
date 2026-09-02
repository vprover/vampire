; The same shape as let-bool-twice.p in SMT-LIB. The SMT-LIB parser has
; always built Boolean let definitions as formulas, so this wrong answer
; predates Boolean $let support in the TPTP parser. The assertion negates a
; conjunction of two tautologies, hence unsatisfiable.
(set-logic ALL)
(declare-fun q () Bool)
(assert (not (and (let ((b (or q (not q)))) b) (let ((d (or q (not q)))) d))))
(check-sat)

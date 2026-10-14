; The shape reported in #908, the same as let-nested-bool.p in SMT-LIB. The
; assertion clausifies to ~q | r and ~q | p, so it is satisfiable on its own.
; -newcnf on used to segfault while clausifying it.
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (let ((b (let ((c (and r p))) c))) (or (=> q b) b)))
(check-sat)

(define-fun foo ((b Bool)) Int (let ((b2 b)) (ite b2 123 456)))
(assert (not (= (foo true) 123)))
(check-sat)
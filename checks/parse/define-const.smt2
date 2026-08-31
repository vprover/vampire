(define-const c Int 5)
(define-fun double ((x Int)) Int (* 2 x))
(assert (not (= (+ (double c) (double c)) (double (+ c c)))))
(check-sat)
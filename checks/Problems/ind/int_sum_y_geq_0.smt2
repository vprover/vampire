
(set-logic UFNIA)

(declare-fun sumY (Int Int) Int)
(assert (forall ((x Int)) (= (sumY x x) x)))
(assert (forall ((x Int) (y Int)) (=> (< x y) (= (sumY x y) (+ y (sumY x (- y 1)))))))

(assert (not (forall ((y Int)) (=> (<= 0 y) (= (* 2 (sumY 0 y)) (* y (+ y 1)))))))

(check-sat)

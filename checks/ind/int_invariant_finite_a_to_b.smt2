(set-logic UFLIA)

(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)

(assert (forall ((x Int)) (=> (and (>= x a) (< x b)) (= (f x) (f (+ x 1))))))

(assert (not (forall ((x Int)) (=> (and (>= x a) (<= x b)) (= (f x) (f a))))))

(check-sat)

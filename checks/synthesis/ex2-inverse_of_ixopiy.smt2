(set-logic UF)

(declare-sort s 0)

(declare-fun inv (s) s)
(declare-fun op (s s) s)

(declare-const e s)

; Left inverse
(assert (forall ((x s)) (= (op (inv x) x) e)))
; Left identity
(assert (forall ((x s)) (= (op e x) x)))
; Associativity
(assert (forall ((x s) (y s) (z s)) (= (op x (op y z)) (op (op x y) z))))

; Conjecture: inverse of products equals the product of the inverse, in opposite order
(assert-synth ((x s) (y s)) ((z s)) (= (op z (op (inv x) (inv y))) e))

(set-option :uncomputable (inv))



(set-logic UFDT)

(declare-datatype Nat ((zero) (s (p Nat))))

(assert-not (forall ((x Nat)) (distinct (s (s (s (s x)))) (s (s (s (s (s x))))))))
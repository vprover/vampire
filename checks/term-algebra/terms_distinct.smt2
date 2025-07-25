(set-logic UFDT)

(declare-datatype Nat ((zero) (s (p Nat))))

(assert-not (distinct (s (s (s (s zero)))) (s (s (s (s (s zero)))))))
(set-logic UFDTLIA)
(declare-datatypes ((Nat 0)) (((succ (pred Nat)) (zero))))
(declare-datatypes ((Lst 0)) (((cons (head Nat) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x) ))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z))) ))

(declare-fun mem (Nat Lst) Bool)
(assert (forall ((x Nat)) (= (mem x nil) false) ))
(assert (forall ((x Nat) (y Nat) (z Lst)) (= (mem x (cons y z)) (or (= x y) (mem x z))) ))

(assert (not (forall ((x Nat) (y Lst) (z Lst)) (=> (mem x y) (mem x (append y z))) )))
(check-sat)

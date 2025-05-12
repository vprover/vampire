(set-logic UFDT)

(declare-sort S 0)
(declare-datatype Lst ((nil) (cons (head S) (tail Lst))))

(define-fun-rec append ((xs Lst) (ys Lst)) Lst
  (match xs ((nil ys)
             ((cons z zs) (cons z (append zs ys))))))

(define-fun-rec mem ((x S) (ys Lst)) Bool
  (match ys ((nil false)
             ((cons z zs) (or (= x z) (mem x zs))))))

(assert-not (forall ((x S) (y Lst) (z Lst)) (=> (mem x y) (mem x (append y z))) ))

(set-logic UFDT)

(declare-sort-parameter A)

(declare-datatype Lst (par (a) ((nil) (cons (head a) (tail (Lst a))))))

(define-fun-rec append ((xs (Lst A)) (ys (Lst A))) (Lst A)
  (match xs ((nil ys)
             ((cons z zs) (cons z (append zs ys))) )))

(define-fun-rec mem ((x A) (ys (Lst A))) Bool
  (match ys ((nil false)
             ((cons z zs) (or (= x z) (mem x zs))) )))

(declare-sort S 0)
(assert-not (forall ((x S) (y (Lst S)) (z (Lst S))) (=> (mem x y) (mem x (append y z))) ))

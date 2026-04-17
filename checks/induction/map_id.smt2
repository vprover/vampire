(set-logic UFDT)

(declare-sort-parameter A)
(declare-sort-parameter B)

(declare-datatype Lst (par (a) ((nil) (cons (head a) (tail (Lst a))))))

(define-fun-rec append ((xs (Lst A)) (ys (Lst A))) (Lst A)
  (match xs ((nil ys)
             ((cons z zs) (cons z (append zs ys))))))

(define-fun-rec map ((f (-> A B)) (xs (Lst A))) (Lst B)
  (match xs ((nil (as nil (Lst B)))
             ((cons y ys) (cons (_ f y) (map f ys))))))

(declare-sort S 0)
(assert-not (forall ((xs (Lst S)) (ys (Lst S))) (= (map (lambda ((x S)) x) xs) xs) ))

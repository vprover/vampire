(set-logic UFDT)

(declare-sort-parameter A)

(declare-datatype lst (par (a) ((nil) (cons (head a) (tail (lst a))))))

(define-fun-rec app ((x (lst A)) (y (lst A))) (lst A)
  (match x ((nil y)
            ((cons x0 x1) (cons x0 (app x1 y))))))

(define-fun-rec suff ((x (lst A)) (y (lst A))) Bool
  (match x ((nil true)
            ((cons x0 x1) (match y ((nil false)
                                    ((cons y0 y1) (or (= (cons x0 x1) (cons y0 y1)) (suff x y1)))))))))

(declare-sort S 0)
(assert-synth ((x1 (lst S)) (x2 (lst S))) ((y (lst S))) (=> (suff x2 x1) (= x1 (app y x2))))

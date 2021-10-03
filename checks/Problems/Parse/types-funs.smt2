(declare-datatypes ((nat 0) (list 0))
  (((zero) (s (s0 nat)))
   ((nil) (cons (head nat) (tail list)))))
(declare-datatype
  tree ((Nil) (node (lc tree) (val nat) (rc tree))))
(define-fun f
    ((x list)) nat
    (match x
        ((nil zero)
        ((cons x0 x1) x0))))
(define-fun-rec r
    ((x tree) (y nat)) nat
    (match x
        ((Nil zero)
        ((node x0 x1 x2)
            (match x0
                ((Nil zero)
                ((node x00 x01 x02)
                    (match y
                        ((zero (f nil))
                        ((s y0) (r x2 y0)))))))))))
(assert (not (= zero (r (node (node Nil (s zero) Nil) zero Nil) (s zero)))))
(check-sat)


(declare-sort S 0)

(assert (not 
  (forall ((arr (Array Int S)) (a S) (b S) (i Int))
    (=>
      (forall ((i Int)) (= (select arr i) a))
      (forall ((i Int) (j Int))
        (and
          (= (select (store (store arr (+ i 1) b) (- i 1) b) i) a)
          (=> (= i j) (= (select (store arr i b) j) b))
        ))
    ))))

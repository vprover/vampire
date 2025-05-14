
(declare-datatype nat ((zero) (s (s_0 nat))))
(declare-datatype list (par (a) ((nil) (cons (head a) (tail (list a))))))
(declare-datatype pair (par (a) ((pair2 (proj1-pair a) (proj2-pair a)))))

(define-funs-rec
  ((even
    ((x nat)) Bool)
   (odd
    ((x nat)) Bool))
  ((match x ((zero true)
             ((s z) (odd z))))
   (match x ((zero false)
             ((s z) (even z))))))

(declare-sort-parameter A)

(define-fun-rec take ((x nat) (y (list A))) (list A)
  (match x
    ((zero (as nil (list A)))
     ((s z)
      (match y
        ((nil (as nil (list A)))
         ((cons z2 xs) (cons z2 (take z xs)))))))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match x
    ((zero y)
     ((s z) (s (plus z y))))))
(define-fun-rec minus ((x nat) (y nat)) nat
  (match x
    ((zero zero)
     ((s z)
      (match y
        (((s y2) (minus z y2))
         (zero zero)))))))
(define-fun-rec third ((x nat)) nat
  (match x
    ((zero zero)
     ((s y)
      (match y
        ((zero zero)
         ((s z)
          (match z
            ((zero zero)
             ((s x2)
              (plus (s zero)
                (third (minus x (s (s (s zero))))))))))))))))
(define-fun-rec leq ((x nat) (y nat)) Bool
  (match x
    ((zero true)
     ((s z)
      (match y
        ((zero false)
         ((s x2) (leq z x2))))))))
(define-fun-rec ordered ((x (list nat))) Bool
  (match x
    ((nil true)
     ((cons y z)
      (match z
        ((nil true)
         ((cons y2 xs) (and (leq y y2) (ordered z)))))))))
(define-fun sort2 ((x nat) (y nat)) (list nat)
  (ite
    (leq x y) (cons x (cons y (as nil (list nat))))
    (cons y (cons x (as nil (list nat))))))
(define-fun-rec length ((x (list A))) nat
  (match x
    ((nil zero)
     ((cons _ l) (plus (s zero) (length l))))))
(define-fun-rec drop ((x nat) (y (list A))) (list A)
  (match x
    ((zero y)
     ((s z)
      (match y
        ((nil (as nil (list A)))
         ((cons z2 xs1) (drop z xs1))))))))
(define-fun splitAt ((x nat) (y (list A))) (pair (list A))
  (pair2 (take x y) (drop x y)))
(define-fun-rec ++ ((x (list A)) (y (list A))) (list A)
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec reverse ((x (list A))) (list A)
  (match x
    ((nil (as nil (list A)))
     ((cons y xs) (++ (reverse xs) (cons y (as nil (list A))))))))
(define-funs-rec
  ((nstooge1sort2
    ((x (list nat))) (list nat))
   (nstoogesort
    ((x (list nat))) (list nat))
   (nstooge1sort1
    ((x (list nat))) (list nat)))
  ((match (splitAt (third (length x)) (reverse x))
     (((pair2 ys1 zs1) (++ (nstoogesort zs1) (reverse ys1)))))
   (match x
     ((nil (as nil (list nat)))
      ((cons y z)
       (match z
         ((nil (cons y (as nil (list nat))))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (nstooge1sort2 (nstooge1sort1 (nstooge1sort2 x))))))))))))
   (match (splitAt (third (length x)) x)
     (((pair2 ys1 zs) (++ ys1 (nstoogesort zs)))))))

(assert-not (let ((two (s (s zero))))
  (and (even two) (not (odd two)) (ordered (nstoogesort (cons two (as nil (list nat))))))))
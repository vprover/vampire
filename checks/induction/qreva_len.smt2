(set-logic UFDT)

(declare-sort S 0)
(declare-datatype Nat ((zero) (s (p Nat))))
(declare-datatype Lst ((nil) (cons (head S) (tail Lst))))

(define-fun-rec plus ((x Nat) (y Nat)) Nat
  (match x ((zero y)
            ((s z) (s (plus z y))))))

(define-fun-rec len ((xs Lst)) Nat
  (match xs ((nil zero)
             ((cons z zs) (s (len zs))))))

(define-fun-rec qreva ((xs Lst) (ys Lst)) Lst
  (match xs ((nil ys)
             ((cons z zs) (qreva zs (cons z ys))))))

(assert-not (forall ((x Lst) (y Lst)) (= (len (qreva x y)) (plus (len x) (len y)))))

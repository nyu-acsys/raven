(set-logic UFLIA)
(declare-fun f (Int) Int)

(declare-const a Int)
(declare-const b Int)

; (assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))
(assert (forall ((x Int)) (<= (f x) (f (+ x 1)))))
(check-sat)
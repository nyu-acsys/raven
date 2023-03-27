; (set-logic UFLIA)
(declare-fun f (Int) Int)

(declare-const a Int)
(declare-const b Int)

; (assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))
(assert (forall ((x Int)) (<= (f x) (f (+ x 1)))))

(declare-const x Real)
(declare-const y Real)
(declare-const $z Real)

(assert (= x (/ 1 3)))
(assert (= y (/ 1 3)))
(assert (= $z (/ 1 3)))

(assert (not (= 1.0000 (+ x y $z))))
(check-sat)
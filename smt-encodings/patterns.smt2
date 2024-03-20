(define-fun h ((x Int) (y Int)) Int 0)
(declare-fun f ((Int)) Int)

(assert (forall ((x Int)) (! (= (h x 0) 0) :pattern ((h x 0)))))
(assert (forall ((x Int)) (! (= (h x 0) 0) :pattern ((h x x)))))
(assert (forall ((x Int)) (! (= (h (f x ) 0) 0) :pattern ((h (f x) 0)))))
(assert (forall ((x Int)) (! (= (f (f x )) 0) :pattern ((f (f x))))))
(assert (forall ((x Int)) (! (= (f (f x )) 0) :pattern ((f x)))))

(assert (forall ((x Int) (y Int)) (! (= (h x y) 0) :pattern ((h (f x) (f y))))))

(assert (forall ((x Int) (y Int)) (! (= (h (f x) (f y)) 0) :pattern ((h x y)))))

(assert (forall ((x Int) (y Int)) (! (= (h x y) 0) :pattern ((f x) (f y)))))
(assert (forall ((x Int) (y Int)) (! (= (h x y) 0) :pattern ((f x) (h x y) (f y)) :pattern ((f x) (f y)))))
(assert (forall ((x Int) (y Int)) (! (= (h x y) 0) :pattern ((f x) (h x y)))))


(assert (forall ((x Int) (y Int)) (! (= (h (h x 0)  y) 0) :pattern ((f x) (h 0 y)))))


(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :timeout 4000)

; (define-fun (par))

; (define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))  ( (g x)  (f y) )  )

; (define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))  ( (g x)  (f y) )  )

(define-fun h ((x Int) (y Int)) Int 0)
(declare-fun f ((Int)) Int)
; (declare-const x (Set Int))
; (declare-const y (Set Int))
; (declare-const z (Set Int))
; (declare-const zz (Array Int Bool))

; (assert (= y ((as const (Set Int)) false)))
; (assert (= x (store 
;        ((as const (Set Int)) false)
;        5
;        true)))
; (assert (= z (intersection x y)))
; (assert (subset y y))
; (assert (not (select z 5)))
; ; (assert (ite (= 5 5) false true))
; (check-sat)
; (get-model)

; (declare-datatypes ((M 0) (N 0)) (((A (A1 Int))) ((B (B1 Int)))))



; ; (declare-datatypes ((M 0) (N 0)) ())

; ; (declare-datatype x ((A (A1 Int))))
; ; (declare-datatype x'y' ((A (A1 Int))))

; (declare-datatype $tuple_1 (par (X0) ( ($tuple_1 ($tuple_1_0 X0)))))
; (declare-datatype x (par (X) ((x (A1 X)))))
; (declare-const zzz (x Int))
; ; (assert (= zzz ((_ as (x Int)) x 5)))

; (assert (= 5 (mod 15 0)))

; ; (define-fun-rec fn ((x Int)) Int (ite (= x 0) x (fn (- x 1))))
; (define-fun-rec fn ((x Int)) Int (fn (- x 1)))
; (define-fun-rec fibonacci ((x Int)) Int (ite (or (= x 0) (= x 1)) 1 (+ (fibonacci (- x 1)) (fibonacci (- x 2)))))

; (assert (forall ((x Int)) (! (= (h x 0) 0) :pattern ((h x 0)))))
; (assert (forall ((x Int)) (! (= (h x 0) 0) :pattern ((h x x)))))
(assert (forall ((x Int)) (! (= (h (f x ) 0) 0) :pattern ((h (f x) 0)))))
; (assert (forall ((x Int)) (! (= (f (f x )) 0) :pattern ((f (f x))))))

; (assert false)
(check-sat)
; (get-unsat-core)
; (assert (= (fn 5) (fn 5)))
; (assert (= (fibonacci 5) 8))
; (check-sat)
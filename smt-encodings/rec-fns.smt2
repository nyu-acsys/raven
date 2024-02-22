(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :timeout 4000)

(define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))  ( (g x)  (f y) )  )

; (define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))  ( (g x)  (f y) )  )

(define-fun h ((x Int) (y Int)) Int 0)

(declare-const x (Set Int))
(declare-const y (Set Int))
(declare-const z (Set Int))
(declare-const zz (Array Int Bool))

(assert (= y ((as const (Set Int)) false)))
(assert (= x (store 
       ((as const (Set Int)) false)
       5
       true)))
(assert (= z (intersection x y)))
(assert (subset y y))
(assert (not (select z 5)))
; (assert (ite (= 5 5) false true))
(check-sat)
(get-model)

(declare-datatypes ((M 0) (N 0)) (((A (A1 Int))) ((B (B1 Int)))))

; (declare-datatypes ((M 0) (N 0)) ())

(declare-datatype x ((A (A1 Int))))
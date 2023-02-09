(set-logic ALL)

(set-option :produce-models true)
(set-option :produce-unsat-cores true)

; A manual encoding of acquire() method from single-node.rav

(declare-sort Loc 0)
(declare-sort Field 0)

(declare-datatype OwnHeapIndex ((OwnIndex (Loc Loc) (Field Field))))

(declare-datatype HeapChunk ((heapNull) (IntChunk (IntVal Int) (IntOwn Real)) (BoolChunk (BoolVal Bool) (BoolOwn Real))))
; separate heaps for each RA, field

(declare-datatype Predicate ((predNull) (lock (lockArg1 Loc) (lockArg2 Bool))))

(declare-fun valid ((Array OwnHeapIndex HeapChunk)) Bool)

(declare-const OwnHeap0 (Array OwnHeapIndex HeapChunk))
(assert (valid OwnHeap0))
(declare-const PredHeap0 (Array Int Predicate))

(assert (
	forall (
		(heap (Array OwnHeapIndex HeapChunk))
		(lf OwnHeapIndex)
		(chunk HeapChunk)
	)

	(=> 
		(and
			(valid heap)
			(= (select heap lf) chunk) 
		)

		(match chunk (
            (heapNull true)
            ((IntChunk i r) (and (<= 0 r) (>= 1 r)))
            ((BoolChunk b r) (and (<= 0 r) (>= 1 r)))
            
        ))
	)
))

; ------------------------------

(declare-const bit Field)
(declare-const bit2 Field)
(assert (distinct bit bit2))

(declare-const l Loc)
(declare-const l2 Loc)
(assert (distinct l l2))
(declare-const b Bool)

; requires lock(l,b)
(assert (= PredHeap0 (store PredHeap0 0 (lock l b))))

; unfold lock(l,b)
(push)
    (assert (not
        (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap0 x) (lock l b))))
    ))
    (check-sat)
(pop)

(declare-const x0 Int)
(assert (and (<= 0 x0) (<= x0 0) (= (select PredHeap0 x0) (lock l b))))

(declare-const PredHeap1 (Array Int Predicate))
(assert (= PredHeap1 (store PredHeap0 x0 (as predNull Predicate))))
; How to get z3 to tell that index 0 is where the relevant chunk is stored?

(declare-const OwnHeap1 (Array OwnHeapIndex HeapChunk))
(assert (valid OwnHeap1))
(assert (= OwnHeap1 (store OwnHeap0 (OwnIndex l bit) (BoolChunk b 1.0))))

; val res: Bool
(declare-const res Bool)

; if (l.bit)
(push)
    ; Asserting ownership over l.bit
    (assert (not (match (select OwnHeap1 (OwnIndex l bit)) (
        (heapNull false)
        ((IntChunk i r) (> r 0))
        ((BoolChunk b r) (> r 0))
    ))))
    (check-sat)
(pop)

; if (l.bit) -- exploring true case
(push)
    (assert (match (select OwnHeap1 (OwnIndex l bit)) (
        (heapNull false)
        ((IntChunk i r) false)
        ((BoolChunk b r) (= b true))
    )))

    ; res := false
    (declare-const res_1 Bool)
    (assert (= res_1 false))

    ; if (res) -- exploring true case
    (push)
        (assert (= res_1 true)) ; this itself is a contradiction

        ; fold lock(l, true)
        ; checking own(l.bit, b)
        (push)
            (assert (not (match (select OwnHeap1 (OwnIndex l bit)) (
                (heapNull false)
                ((IntChunk i r) false)
                ((BoolChunk b r) (and (= r 1) (= b true)))
            ))))
            (check-sat)
        (pop)

        (declare-const OwnHeap2 (Array OwnHeapIndex HeapChunk))
        (assert (valid OwnHeap2))
        (assert (= OwnHeap2 (store OwnHeap1 (OwnIndex l bit) (as heapNull HeapChunk))))

        (declare-const PredHeap2 (Array Int Predicate))
        (assert (= PredHeap2 (store PredHeap1 0 (lock l true))))

        ; commitAU(phi)
        (push)
            (assert (not (and (= b false) (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap0 x) (lock l true)))))))
            (check-sat)
        (pop)

    (pop)

    ; if (res) -- exploring false case
    (push)
        (assert (= res_1 false))

        ; fold lock(l, true) // Check in code if this should be `fold lock(l, true)` or `fold lock(l, false)`
        (push)
            (assert (not (match (select OwnHeap1 (OwnIndex l bit)) (
                (heapNull false)
                ((IntChunk i r) false)
                ((BoolChunk b r) (and (= r 1) (= b true)))
            ))))
            (check-sat)
        (pop)

        (declare-const OwnHeap2 (Array OwnHeapIndex HeapChunk))
        (assert (valid OwnHeap2))
        (assert (= OwnHeap2 (store OwnHeap1 (OwnIndex l bit) (as heapNull HeapChunk))))

        (declare-const b_1 Bool)
        (declare-const PredHeap2 (Array Int Predicate))
        (assert (= PredHeap2 (store PredHeap1 0 (lock l b_1))))
        
        ; abortAU(phi)
        (push)
            (assert (not
                (exists ((x Int) (b Bool)) (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l b))))
            ))
            (check-sat)
        (pop)

        ; if (!res)
        (assert (= res_1 false))

        ; acquire(l)

        ; exhale pre-condition
        ; ensure we have lock(l,b)
        (declare-const b_2 Bool)
        (push)
            (assert (not
                (exists ((x Int) (b_2 Bool)) (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l b_2))))
            ))
            ; How to connect b_2 above to b_2 in the PredHeap2? Removing quantifier over b_2 in above stmt yields `unknown` because it can possibly set the wrong value for b_2. Need to do so to assert in the postcondition that b_2 = false.
            (check-sat)
        (pop)

        (declare-const x Int)
        
        (assert 
             (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l b_2)))
        )

        ; exhale
        (declare-const PredHeap3 (Array Int Predicate))
        (assert (= PredHeap3 (store PredHeap2 0 (as predNull Predicate))))

        ; inhale postcondition
        (declare-const PredHeap4 (Array Int Predicate))
        (assert (= PredHeap4 (store PredHeap3 0 (lock l true))))
        (assert (= b_2 false)) ; this statement currently is meaningless since b_2 is just a free variable. Want to bind it to the value on the PredHeap2.

        ; assert postcondition
        (push)
            (assert (not (and (= b_2 false) (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap4 x) (lock l true)))))))
            (check-sat)
        (pop)




    (pop)
(pop)

; if (l.bit) -- exploring false case
(push)
    (assert (match (select OwnHeap1 (OwnIndex l bit)) (
        (heapNull false)
        ((IntChunk i r) false)
        ((BoolChunk b r) (and (= b false) (> r 0)))
    )))

    ; l.bit = true
    (push)
        ; Asserting ownership over l.bit
        (assert (not (match (select OwnHeap1 (OwnIndex l bit)) (
            (heapNull false)
            ((IntChunk i r) false)
            ((BoolChunk b r) (= r 1))
        ))))
        (check-sat)
    (pop)

    (declare-const OwnHeap2 (Array OwnHeapIndex HeapChunk))
    (assert (valid OwnHeap2))
    (assert (= OwnHeap2 (store OwnHeap1 (OwnIndex l bit) (BoolChunk true 1.0))))

    ; res := true
    (declare-const res_1 Bool)
    (assert (= res_1 true))

    ; if (res) -- exploring true case
    (push)
        (assert (= res_1 true))

        ; fold lock(l, true)
        ; checking own(l.bit, b)
        (push)
            (assert (not (match (select OwnHeap2 (OwnIndex l bit)) (
                (heapNull false)
                ((IntChunk i r) false)
                ((BoolChunk b r) (and (= r 1) (= b true)))
            ))))
            (check-sat)
        (pop)

        (declare-const OwnHeap3 (Array OwnHeapIndex HeapChunk))
        (assert (valid OwnHeap3))
        (assert (= OwnHeap3 (store OwnHeap2 (OwnIndex l bit) (as heapNull HeapChunk))))

        (declare-const PredHeap2 (Array Int Predicate))
        (assert (= PredHeap2 (store PredHeap1 0 (lock l true))))

        ; commitAU(phi)
        (push)
            (assert (not (and (= b false) (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l true)))))))
            (check-sat)
        (pop)
    (pop)

    ; if (res) -- exploring false case
    (push)
        (assert (= res_1 false))

        ; fold lock(l, true) // Check in code if this should be `fold lock(l, true)` or `fold lock(l, false)`
        (push)
            (assert (not (match (select OwnHeap2 (OwnIndex l bit)) (
                (heapNull false)
                ((IntChunk i r) false)
                ((BoolChunk b r) (and (= r 1) (= b true)))
            ))))
            (check-sat)
        (pop)

        (declare-const OwnHeap3 (Array OwnHeapIndex HeapChunk))
        (assert (valid OwnHeap3))
        (assert (= OwnHeap3 (store OwnHeap2 (OwnIndex l bit) (as heapNull HeapChunk))))

        (declare-const b_1 Bool)
        (declare-const PredHeap2 (Array Int Predicate))
        (assert (= PredHeap2 (store PredHeap1 0 (lock l b_1))))
        
        ; abortAU(phi)
        (push)
            (assert (not
                (exists ((x Int) (b Bool)) (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l b))))
            ))
            (check-sat)
        (pop)

        ; if (!res)
        (assert (= res_1 false))

        ; acquire(l)

        ; exhale pre-condition
        ; ensure we have lock(l,b)
        (declare-const b_2 Bool)
        (push)
            (assert (not
                (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap2 x) (lock l b_2))))
            ))
            (check-sat)
        (pop)

        ; exhale
        (declare-const PredHeap3 (Array Int Predicate))
        (assert (= PredHeap3 (store PredHeap2 0 (as predNull Predicate))))

        ; inhale postcondition
        (declare-const PredHeap4 (Array Int Predicate))
        (assert (= PredHeap4 (store PredHeap3 0 (lock l true))))
        (assert (= b_2 false))

        ; assert postcondition
        (push)
            (assert (not (and (= b false) (exists ((x Int)) (and (<= 0 x) (<= x 0) (= (select PredHeap4 x) (lock l true)))))))
            (check-sat)
        (pop)
    (pop)
(pop)
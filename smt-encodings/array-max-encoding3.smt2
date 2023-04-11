(set-logic ALL)

; (set-option :produce-models true)
(set-option :smt.mbqi false)
; (set-option :produce-unsat-cores true)
(set-option :timeout 2000)

; A manual encoding of max() from array-max.rav

(declare-sort Loc 0)
(declare-sort Field 1)
; Fields to be separated by type

(declare-datatype FracHeapChunk (par (T) ((FracHeapNull) (FracChunkConstr (Val T) (Own Real)) (FracHeapTop))))
; separate heaps for each RA, field

(declare-datatype HeapChunk (par (T) ((HeapNull) (Chunk (Val T)))))

(define-sort FracOwnHeap (T) (Array Loc (FracHeapChunk T)))
(define-sort OwnHeap (T) (Array Loc (HeapChunk T)))

(define-sort PredHeap (T) (Array T Int))

(define-fun IntFracChunkAdd ((x1 (FracHeapChunk Int)) (x2 (FracHeapChunk Int))) (FracHeapChunk Int) 
    (match x1 (
        (FracHeapNull x2)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull x1)
            ((FracChunkConstr v2 r2) (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2)) (as FracHeapTop (FracHeapChunk Int))))
            (FracHeapTop (as FracHeapTop (FracHeapChunk Int)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Int)))
    ))
)

(define-fun IntFracChunkSubtract ((x1 (FracHeapChunk Int)) (x2 (FracHeapChunk Int))) (FracHeapChunk Int) 
    (match x2 (
        (FracHeapNull x1)
        ((FracChunkConstr v2 r2) (match x1 (
            (FracHeapNull (as FracHeapTop (FracHeapChunk Int)))
            ((FracChunkConstr v1 r1) 
                (ite (= v1 v2) 
                    (ite (= r1 r2) 
                        (as FracHeapNull (FracHeapChunk Int))
                        (ite (> r1 r2) 
                            (FracChunkConstr v1 (- r1 r2))
                            (as FracHeapTop (FracHeapChunk Int))        
                        )
                    )

                    (as FracHeapTop (FracHeapChunk Int))
                )
            )
            (FracHeapTop (as FracHeapTop (FracHeapChunk Int)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Int)))
    ))
)

(declare-fun IntHeapValid ((FracOwnHeap Int)) Bool)
(assert (
	forall (
		(heap (FracOwnHeap Int))
		(l Loc)
		(chunk (FracHeapChunk Int))
	)

	(=> 
		(and
			(IntHeapValid heap)
			(= (select heap l) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunkConstr i r) (and (<= 0 r) (>= 1 r)))
            (FracHeapTop false)
        ))
	)
))

(declare-fun IntHeapChunkCompare ((x1 (FracHeapChunk Int)) (x2 (FracHeapChunk Int))) Bool 
    (match x1 (
        (FracHeapNull true)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull false)
            ((FracChunkConstr v2 r2) (ite (= v1 v2)
                (<= r1 r2) false
            ))
            (FracHeapTop false)
        )))
        (FracHeapTop false)
    ))
) 

(define-fun BoolFracChunkAdd ((x1 (FracHeapChunk Bool)) (x2 (FracHeapChunk Bool))) (FracHeapChunk Bool) 
    (match x1 (
        (FracHeapNull x2)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull x1)
            ((FracChunkConstr v2 r2) (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2)) (as FracHeapTop (FracHeapChunk Bool))))
            (FracHeapTop (as FracHeapTop (FracHeapChunk Bool)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Bool)))
    ))
)

(define-fun BoolFracChunkSubtract ((x1 (FracHeapChunk Bool)) (x2 (FracHeapChunk Bool))) (FracHeapChunk Bool) 
    (match x2 (
        (FracHeapNull x1)
        ((FracChunkConstr v2 r2) (match x1 (
            (FracHeapNull (as FracHeapTop (FracHeapChunk Bool)))
            ((FracChunkConstr v1 r1) 
                (ite (= v1 v2) 
                    (ite (= r1 r2) 
                        (as FracHeapNull (FracHeapChunk Bool))
                        (ite (> r1 r2) 
                            (FracChunkConstr v1 (- r1 r2))
                            (as FracHeapTop (FracHeapChunk Bool))        
                        )
                    ) 
                    (as FracHeapTop (FracHeapChunk Bool))
                )
            )
            (FracHeapTop (as FracHeapTop (FracHeapChunk Bool)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Bool)))
    ))
)

(declare-fun BoolHeapValid ((FracOwnHeap Bool)) Bool)
(assert (
	forall (
		(heap (FracOwnHeap Bool))
		(l Loc)
		(chunk (FracHeapChunk Bool))
	)

	(=> 
		(and
			(BoolHeapValid heap)
			(= (select heap l) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunkConstr i r) (and (<= 0 r) (>= 1 r)))
            (FracHeapTop false)
        ))
	)
))

; ---------------------------------

(declare-sort IArray 0)
(declare-fun loc (IArray Int) Loc)
(declare-fun len (IArray) Int)
(declare-fun first (Loc) IArray)
(declare-fun second (Loc) Int)

; lemma all-diff
(assert (
    forall ((a IArray) (i Int)) 
        (and (= (first (loc a i)) a) (= (second (loc a i)) i))
))

; lemma len_nonneg
(assert (
    forall ((a IArray))
        (>= (len a) 0)
))

; field value: Int
(declare-const value (Field Int))

(declare-datatype isMaxPred ((isMaxPredConstr (isMaxPredArg1 Int) (ixMaxPredArg2 (Array Int Int)) (isMaxPredArg3 Int))))
(define-sort isMaxPredHeap () (PredHeap isMaxPred))

(declare-datatype arrPred ((arrPredConstr (arrPredArg1 IArray) (arrPredArg2 (Array Int Int)))))
(define-sort arrPredHeap () (PredHeap arrPred))

; ---------------------------------

(declare-const a_0 IArray)
(declare-const m_0 (Array Int Int))
(declare-const x_0 Int)

(declare-const isMaxPredHeap_0 isMaxPredHeap)
(assert (forall ((index isMaxPred)) (= 0 (select isMaxPredHeap_0 index))))

(declare-const arrPredHeap_0 arrPredHeap)
(assert (forall ((index arrPred)) (= 0 (select arrPredHeap_0 index))))

(declare-const valueOwnHeap_0 (FracOwnHeap Int))
(assert (IntHeapValid valueOwnHeap_0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk Int)) (select valueOwnHeap_0 index))))

; requires arr(a,m)
(declare-const arrPredHeap_1 arrPredHeap)
(assert (= (+ (select arrPredHeap_0 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_1 (arrPredConstr a_0 m_0))))
(assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_0 index) (select arrPredHeap_1 index)))))

; (echo "SAT/Unknown 1:")
; (check-sat)

; if (len(a) == 0)
(push)
    (assert (= (len a_0) 0))
    (declare-const x_1 Int)
    (assert (= x_1 (- 1)))

    ; checking postconditions

    (push)
        (assert (not
            (<= 1 (select arrPredHeap_1 (arrPredConstr a_0 m_0)))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (ite (= (len a_0) 0) (= x_1 (- 1)) (and (<= 0 x_1) (< x_1 (len a_0))))
        ))
        (check-sat)
    (pop)

    ; (echo "SAT/Unknown 2:")
    ; (check-sat)

    (push)
    ; fails -- manually unfolding and proving body of predicate in next request.
        (echo "Fails:")
        (assert (not
            (<= 1 (select isMaxPredHeap_0 (isMaxPredConstr x_1 m_0 (len a_0))))
        ))
        
        (check-sat)
    (pop)

    (push)
        (assert (not
            (forall ((j Int)) (=> (and (<= 0 j) (< j (len a_0))) (<= (select m_0 j) (select m_0 x_1))))
        ))
        (check-sat)
    (pop)
(pop)

; else
(push)
    (assert (not (= (len a_0) 0)))

    (declare-const y_0 Int)
    (declare-const x_1 Int)
    (assert (= x_1 0))
    (assert (= y_0 (- (len a_0) 1)))

    ; while loop
    ; proving invariants before loop is executed
    (push)
        (assert (not
            (<= 1 (select arrPredHeap_1 (arrPredConstr a_0 m_0)))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (and (<= 0 x_1) (<= x_1 y_0) (< y_0 (len a_0)))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (or 
                (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y_0 i) (< i (len a_0)))) (< (select m_0 i) (select m_0 x_1))))
                (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y_0 i) (< i (len a_0)))) (<= (select m_0 i) (select m_0 y_0))))
            )
        ))
        (check-sat)
    (pop)

    ; abstracting over while loop

    ; exhale invariants
    (declare-const arrPredHeap_2 (PredHeap arrPred))
    (assert (= (- (select arrPredHeap_1 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_2 (arrPredConstr a_0 m_0))))
    (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_1 index) (select arrPredHeap_2 index)))))

    ; havoc loop variables
    (declare-const x_2 Int)
    (declare-const y_1 Int)

    ; checking properties of while loop
    (push)
        ; setting up pre-state before execution of loop iteration

        ; inhaling invariant
        ; here _0 for every heap is treated as the completely empty heap
        (declare-const arrPredHeap_3 (PredHeap arrPred))
        (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_2 index) (select arrPredHeap_3 index)))))
        (assert (= (+ (select arrPredHeap_2 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_3 (arrPredConstr a_0 m_0))))

        (declare-const isMaxPredHeap_1 (PredHeap isMaxPred))
        (assert (forall ((index isMaxPred)) (= (select isMaxPredHeap_0 index) (select isMaxPredHeap_1 index))))

        (declare-const valueOwnHeap_1 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_1))
        (assert (forall ((index Loc)) (= (select valueOwnHeap_0 index) (select valueOwnHeap_1 index))))

        (assert (and (<= 0 x_2) (<= x_2 y_1) (< y_1 (len a_0))))
        (assert (or 
            (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a_0)))) (< (select m_0 i) (select m_0 x_2))))
            (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a_0)))) (<= (select m_0 i) (select m_0 y_1))))
        ))
        

        ; inhaling loop condition
        (assert (not (= x_2 y_1)))

        ; executing loop iteration
        ; unfold arr(a,m)
        ; checking ownership
        (push)
            (assert (not
                (<= 1 (select arrPredHeap_3 (arrPredConstr a_0 m_0)))
            ))
            (check-sat)
        (pop)

        ; unfolding

        ; exhaling from arrPredHeap
        (declare-const arrPredHeap_4 (PredHeap arrPred))
        (assert (= (- (select arrPredHeap_3 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_4 (arrPredConstr a_0 m_0))))
        (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_3 index) (select arrPredHeap_4 index)))))

        ; need to detect that arrPred body talks about valueOwnHeap


        ; First checking injectivity of mapping
        (push)
            (assert (not 
                (forall ((i Int) (j Int)) (=> (and (<= 0 i) (< i (len a_0)) (<= 0 j) (< j (len a_0)) (not (= i j))) (not (= (loc a_0 i) (loc a_0 j)))))
            ))

            (check-sat)
        (pop)


        ; Here the below chunks need to be added to existing chunks in valueOwnHeap_1.
        (declare-const valueOwnHeap_2 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_2))
        (assert (forall 
            ((j Int)) 
            (! (=> 
                (and (<= 0 j) (< j (len a_0)))
                (= (IntFracChunkAdd (select valueOwnHeap_1 (loc a_0 j)) (FracChunkConstr (select m_0 j) 1)) (select valueOwnHeap_2 (loc a_0 j)))
            ) :pattern ((select valueOwnHeap_2 (loc a_0 j))) )
        ))

        ; Frame the rest of the existing heap
        (assert (forall 
            ((l Loc)) 
            (or 
                ; l is quantified over by the separating star
                (exists ((j Int)) (and (<= 0 j) (< j (len a_0)) (= l (loc a_0 j))))

                ; or l preserves its value in valueOwnHeap
                (= (select valueOwnHeap_1 l) (select valueOwnHeap_2 l))
            )
        ))
        
        ; (echo "SAT/Unknown 3:")
        ; (check-sat)


        ; if (loc(a, x).value <= loc(a, y).value)

        ; checking ownership over loc(a, x).value and loc(a, y).value
        (push)
            (assert (not
                (exists ((val Int) (perm Real)) (and (= (FracChunkConstr val perm) (select valueOwnHeap_2 (loc a_0 x_2))) (> perm 0)))
            ))
            (check-sat)
        (pop)

        (push)
            (assert (not
                (exists ((val Int) (perm Real)) (and (= (FracChunkConstr val perm) (select valueOwnHeap_2 (loc a_0 y_1))) (> perm 0)))
            ))
            (check-sat)
        (pop)

        (push)
            (assert (<= (Val (select valueOwnHeap_2 (loc a_0 x_2))) (Val (select valueOwnHeap_2 (loc a_0 y_1)))))

            ; x := x + 1
            (declare-const x_3 Int)
            (assert (= x_3 (+ x_2 1)))

            ; fold arr(a,m)
            ; checking ownership
            (push)
                (assert (not 
                    (forall 
                        ((j Int)) 

                        (=> 
                            (and (<= 0 j) (< j (len a_0))) 
                            (= (FracChunkConstr (select m_0 j) 1) (select valueOwnHeap_2 (loc a_0 j)))
                        )
                    )
                ))
                (check-sat)
            (pop)

            (declare-const valueOwnHeap_3 (FracOwnHeap Int))
            (assert (IntHeapValid valueOwnHeap_3))
            (assert (forall 
                ((j Int)) 
                (! (=> 
                    (and (<= 0 j) (< j (len a_0)))
                    (= (IntFracChunkSubtract (select valueOwnHeap_2 (loc a_0 j)) (FracChunkConstr (select m_0 j) 1)) (select valueOwnHeap_3 (loc a_0 j)))
                ) :pattern ((select valueOwnHeap_3 (loc a_0 j))) )
            ))

            ; Frame the rest of the existing heap
            (assert (forall 
                ((l Loc))
                (or 
                    ; l is quantified over by the separating star
                    (exists ((j Int)) (and (<= 0 j) (< j (len a_0)) (= l (loc a_0 j))))

                    ; or l preserves its value in valueOwnHeap
                    (= (select valueOwnHeap_2 l) (select valueOwnHeap_3 l))
                )
            ))

            (declare-const arrPredHeap_5 (PredHeap arrPred))
            (assert (= (+ (select arrPredHeap_4 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_5 (arrPredConstr a_0 m_0))))
            (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_4 index) (select arrPredHeap_5 index)))))


            ; (echo "SAT/Unknown 4:")
            ; (check-sat)

            ; re-establishing invariants

            (push)
                (assert (not
                    (<= 1 (select arrPredHeap_5 (arrPredConstr a_0 m_0)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (and (<= 0 x_3) (<= x_3 y_1) (< y_1 (len a_0)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (or 
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_3)) (and (< y_1 i) (< i (len a_0)))) (< (select m_0 i) (select m_0 x_3))))
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_3)) (and (< y_1 i) (< i (len a_0)))) (<= (select m_0 i) (select m_0 y_1))))
                    )
                ))
                (check-sat)
            (pop)
        (pop)

        ; else
        (push)
            (assert (not (<= (Val (select valueOwnHeap_2 (loc a_0 x_2))) (Val (select valueOwnHeap_2 (loc a_0 y_1))))))

            ; y := y - 1
            (declare-const y_2 Int)
            (assert (= y_2 (- y_1 1)))

            ; fold arr(a,m)
            ; checking ownership
            (push)
                (assert (not 
                    (forall 
                        ((j Int)) 

                        (=> 
                            (and (<= 0 j) (< j (len a_0))) 
                            (= (FracChunkConstr (select m_0 j) 1) (select valueOwnHeap_2 (loc a_0 j)))
                        )
                    )
                ))
                (check-sat)
            (pop)

            (declare-const valueOwnHeap_3 (FracOwnHeap Int))
            (assert (IntHeapValid valueOwnHeap_3))
            (assert (forall 
                ((j Int)) 
                (! (=> 
                    (and (<= 0 j) (< j (len a_0)))
                    (= (IntFracChunkSubtract (select valueOwnHeap_2 (loc a_0 j)) (FracChunkConstr (select m_0 j) 1)) (select valueOwnHeap_3 (loc a_0 j)))
                ) :pattern ((select valueOwnHeap_3 (loc a_0 j))) )
            ))

            ; Frame the rest of the existing heap
            (assert (forall 
                ((l Loc))
                (or 
                    ; l is quantified over by the separating star
                    (exists ((j Int)) (and (<= 0 j) (< j (len a_0)) (= l (loc a_0 j))))

                    ; or l preserves its value in valueOwnHeap
                    (= (select valueOwnHeap_2 l) (select valueOwnHeap_3 l))
                )
            ))

            (declare-const arrPredHeap_5 (PredHeap arrPred))
            (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_4 index) (select arrPredHeap_5 index)))))
            (assert (= (+ (select arrPredHeap_4 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_5 (arrPredConstr a_0 m_0))))


            ; (echo "SAT/Unknown 5:")
            ; (check-sat)

            ; re-establishing invariants

            (push)
                (assert (not
                    (<= 1 (select arrPredHeap_5 (arrPredConstr a_0 m_0)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (and (<= 0 x_2) (<= x_2 y_2) (< y_2 (len a_0)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (or 
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_2 i) (< i (len a_0)))) (< (select m_0 i) (select m_0 x_2))))
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_2 i) (< i (len a_0)))) (<= (select m_0 i) (select m_0 y_2))))
                    )
                ))
                (check-sat)
            (pop)
        (pop)
    (pop)


    ; asserting negation of looping condition
    (assert (= x_2 y_1))

    ; inhale invariant
    (declare-const arrPredHeap_3 (PredHeap arrPred))
    (assert (= (+ (select arrPredHeap_2 (arrPredConstr a_0 m_0)) 1) (select arrPredHeap_3 (arrPredConstr a_0 m_0))))
    (assert (forall ((index arrPred)) (=> (not (= index (arrPredConstr a_0 m_0))) (= (select arrPredHeap_2 index) (select arrPredHeap_3 index)))))

    (assert (and (<= 0 x_2) (<= x_2 y_1) (< y_1 (len a_0))))

    (assert (or 
        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a_0)))) (< (select m_0 i) (select m_0 x_2))))
        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a_0)))) (<= (select m_0 i) (select m_0 y_1))))
    ))
    
    ; checking postconditions

    (push)
        (assert (not
            (<= 1 (select arrPredHeap_3 (arrPredConstr a_0 m_0)))
        ))

        (check-sat)
    (pop)

    (push)
        (assert (not
            (ite (= (len a_0) 0) (= x_2 -1) (and (<= 0 x_2) (< x_2 (len a_0))))
        ))

        (check-sat)
    (pop)

    ; (echo "SAT/Unknown 6:")
    ; (check-sat)

    (push)
    ; fails -- manually unfolding and proving body of predicate in next request.
        (echo "Fails:")
        (assert (not
            (<= 1 (select isMaxPredHeap_0 (isMaxPredConstr x_2 m_0 (len a_0))))
        ))
        
        (check-sat)
    (pop)

    (push)
        (assert (not
            (forall ((j Int)) (=> (and (<= 0 j) (< j (len a_0))) (<= (select m_0 j) (select m_0 x_2))))
        ))
        (check-sat)
    (pop)
(pop)
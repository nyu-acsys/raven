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

(declare-sort IArray)
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

(declare-datatype orderedPred ((orderedPredConstr (orderedPredArg1 (Array Int Int)) (orderedPredArg2 Int) (orderedPredArg3 Int))))
(define-sort orderedPredHeap () (PredHeap orderedPred))

(declare-datatype accessPred ((accessPredConstr (accessPredArg1 IArray) (accessPredArg2 (Array Int Int)))))
(define-sort accessPredHeap () (PredHeap accessPred))

; ------------------------------

(declare-const a_0 IArray)
(declare-const m_0 (Array Int Int))

(declare-const orderedPredHeap_0 orderedPredHeap)
(assert (forall ((index orderedPred)) (= 0 (select orderedPredHeap_0 index))))

(declare-const accessPredHeap_0 accessPredHeap)
(assert (forall ((index accessPred)) (= 0 (select accessPredHeap_0 index))))

(declare-const valueOwnHeap_0 (FracOwnHeap Int))
(assert (IntHeapValid valueOwnHeap_0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk Int)) (select valueOwnHeap_0 index))))


; requires access(a,m)
(declare-const accessPredHeap_1 accessPredHeap)
(assert (= (+ (select accessPredHeap_0 (accessPredConstr a_0 m_0)) 1) (select accessPredHeap_1 (accessPredConstr a_0 m_0))))
(assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_0))) (= (select accessPredHeap_0 index) (select accessPredHeap_1 index)))))



; how do we deal with this kind of separating conjunction apriori? Proving injectivity and such.
; requires forall i: Int :: 0 <= i && i < len(a) ==> loc(a,i).value == 0 || loc(a,i).value == 1 || loc(a,i) == 2

; checking injectivity

; (push)
;     (assert (not 
;         (forall ((i Int) (j Int)) (=> (and (<= 0 i) (< i (len a_0)) (<= 0 j) (< j (len a_0)) (not (= i j))) (not (= (loc a_0 i) (loc a_0 j)))))
;     ))

;     (check-sat)
; (pop)


; (declare-const valueOwnHeap_1 (FracOwnHeap Int))
; (assert (IntHeapValid valueOwnHeap_1))
; (assert (forall ((i Int)) 
;     (=> (and (<= 0 i) (< i (len a_0)))
;         (or (= (IntFracChunkAdd (select valueOwnHeap_0 (loc a_0 i)) (FracChunkConstr 0 1)) (select valueOwnHeap_1 (loc a_0 i)))
;             (= (IntFracChunkAdd (select valueOwnHeap_0 (loc a_0 i)) (FracChunkConstr 1 1)) (select valueOwnHeap_1 (loc a_0 i)))
;             (= (IntFracChunkAdd (select valueOwnHeap_0 (loc a_0 i)) (FracChunkConstr 2 1)) (select valueOwnHeap_1 (loc a_0 i)))
;         )
;     )
; ))

; ; framing the rest of the heap
; (assert (forall 
;     ((l Loc)) 
;     (or 
;         ; l is quantified over by the separating star
;         (exists ((i Int)) (and (<= 0 i) (< i (len a_0)) (= l (loc a_0 i))))

;         ; or l preserves its value in valueOwnHeap
;         (= (select valueOwnHeap_0 l) (select valueOwnHeap_1 l))
;     )
; ))

; requires forall i: Int :: 0 <= i && i < len(a) ==> m[i] == 0 || m[i] == 1 || m[i] == 2

(assert (forall ((i Int)) 
    (=> (and (<= 0 i) (< i (len a_0))) 
        (or 
            (= 0 (select m_0 i))
            (= 1 (select m_0 i))
            (= 2 (select m_0 i))
        )
    )
))


(declare-const unsorted_0 Int)
(assert (= 0 unsorted_0))

(declare-const white_0 Int)
(assert (= 0 white_0))

(declare-const blue_0 Int)
(assert (= (len a_0) blue_0))

; exhale invariants

; invariant access(a, m)
(push)
    (assert (not 
        (<= 1 (select accessPredHeap_1 (accessPredConstr a_0 m_0)))
    ))
    (check-sat)
(pop)


(declare-const accessPredHeap_2 accessPredHeap)
(assert (= (- (select accessPredHeap_1 (accessPredConstr a_0 m_0)) 1) (select accessPredHeap_2 (accessPredConstr a_0 m_0))))
(assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_0))) (= (select accessPredHeap_1 index) (select accessPredHeap_2 index)))))


; invariant 0 <= white && white <= unsorted && unsorted <= blue && blue <= len(a)
(push)
    (assert (not
        (and (<= 0 white_0) (<= white_0 unsorted_0) (<= unsorted_0 blue_0) (<= blue_0 (len a_0)))
    ))
    (check-sat)
(pop)

; invariant forall i: Int :: 0 <= i && i < len(a) ==> m[i] == 0 || m[i] == 1 || m[i] == 2
(push)
    (assert (not 
        (forall ((i Int)) (=> (and (<= 0 i) (< i (len a_0))) 
            (or 
                (= 0 (select m_0 i))
                (= 1 (select m_0 i))
                (= 2 (select m_0 i))
            )
        ))
    ))
(pop)

; invariant forall i : Int :: 0 <= i && i < white ==> m[i] == 0
(push)
    (assert (not 
        (forall ((i Int)) (=> (and (<= 0 i)  (< i white_0)) (= 0 (select m_0 i))))
    ))
    (check-sat)
(pop)

; invariant forall i : Int :: white <= i && i < unsorted ==> m[i] == 1
(push)
    (assert (not 
        (forall ((i Int)) (=> (and (<= white_0 i)  (< i unsorted_0)) (= 1 (select m_0 i))))
    ))
    (check-sat)
(pop)

; invariant forall i : Int :: blue <= i && i < len(a) ==> m[i] == 2
(push)
    (assert (not 
        (forall ((i Int)) (=> (and (<= blue_0 i)  (< i (len a_0))) (= 2 (select m_0 i))))
    ))
    (check-sat)
(pop)

; havoc loop variables
(declare-const white_1 Int)
(declare-const blue_1 Int)
(declare-const unsorted_1 Int)
(declare-const m_1 (Array Int Int))

; inhaling invariant

(declare-const accessPredHeap_3 accessPredHeap)
(assert (= (+ (select accessPredHeap_2 (accessPredConstr a_0 m_1)) 1)(select accessPredHeap_3 (accessPredConstr a_0 m_1))))
(assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_1))) (= (select accessPredHeap_2 index) (select accessPredHeap_3 index)))))

(assert (and (<= 0 white_1) (<= white_1 unsorted_1) (<= unsorted_1 blue_1) (<= blue_1 (len a_0))))

(assert
    (forall ((i Int)) (=> (and (<= 0 i) (< i (len a_0))) 
        (or 
            (= 0 (select m_1 i))
            (= 1 (select m_1 i))
            (= 2 (select m_1 i))
        )
    ))
)

(assert (forall ((i Int)) (=> (and (<= 0 i) (< i white_1)) (= 0 (select m_1 i)))))

(assert (forall ((i Int)) (=> (and (<= white_1 i) (< i unsorted_1)) (= 1 (select m_1 i)))))

(assert (forall ((i Int)) (=> (and (<= blue_1 i) (< i (len a_0))) (= 2 (select m_1 i)))))

(push)
    ; inhaling loop condition

    (assert (< unsorted_1 blue_1))

    ; unfold access(a,m)
    (declare-const accessPredHeap_4 accessPredHeap)
    (assert (= (- (select accessPredHeap_3 (accessPredConstr a_0 m_1)) 1)(select accessPredHeap_4 (accessPredConstr a_0 m_1))))
    (assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_1))) (= (select accessPredHeap_3 index) (select accessPredHeap_4 index)))))

    (declare-const valueOwnHeap_1 (FracOwnHeap Int))
    (assert (IntHeapValid valueOwnHeap_1))
    (assert (forall ((i Int)) 
        (=> 
            (and (<= 0 i) (< i (len a_0)))
            (= (IntFracChunkAdd (select valueOwnHeap_0 (loc a_0 i)) (FracChunkConstr (select m_1 i) 1)) (select valueOwnHeap_1 (loc a_0 i)))
        )
    ))


    (assert (forall ((index Loc)) 
        (or 
            (exists ((i Int)) (and (<= 0 i) (< i (len a_0)) (= index (loc a_0 i))))
            (= (select valueOwnHeap_1 index) (select valueOwnHeap_0 index))
        )
    ))

    ; var tmp : Int := loc(a,unsorted).value;

    ; checking permission

    (push)
        (assert (not 
            (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_1 (loc a_0 unsorted_1)) (FracChunkConstr val perm)) (> perm 0)))
        ))
        (check-sat)
    (pop)

    (declare-const tmp_0 Int)
    (assert (= tmp_0 (Val (select valueOwnHeap_1 (loc a_0 unsorted_1)))))

    ; if (tmp == 1)
    (push)
        (assert (= tmp_0 1))
        
        (declare-const unsorted_2 Int)
        (assert (= unsorted_2 (+ unsorted_1 1)))

        ; fold access(a, m)

        ; check permission
        (push)
            (assert (not 
                (forall ((i Int)) 
                    (=> 
                        (and (<= 0 i) (< i (len a_0))) 
                        (= (select valueOwnHeap_1 (loc a_0 i)) (FracChunkConstr (select m_1 i) 1))    
                    )
                )
            ))
            (check-sat)
        (pop)

        (declare-const accessPredHeap_5 accessPredHeap)
        (assert (= (+ (select accessPredHeap_4 (accessPredConstr a_0 m_1)) 1)(select accessPredHeap_5 (accessPredConstr a_0 m_1))))
        (assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_1))) (= (select accessPredHeap_4 index) (select accessPredHeap_5 index)))))


        (declare-const valueOwnHeap_2 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_2))
        (assert (forall ((i Int)) 
            (=> 
                (and (<= 0 i) (< i (len a_0)))
                (= (IntFracChunkSubtract (select valueOwnHeap_1 (loc a_0 i)) (FracChunkConstr (select m_1 i) 1)) (select valueOwnHeap_2 (loc a_0 i)))
            )
        ))


        (assert (forall ((index Loc)) 
            (or 
                (exists ((i Int)) (and (<= 0 i) (< i (len a_0)) (= index (loc a_0 i))))
                (= (select valueOwnHeap_2 index) (select valueOwnHeap_1 index))
            )
        ))

        ; re-establishing Invariants

        ; invariant access(a, m)

        (push)
            (assert (not 
                (<= 1 (select accessPredHeap_5 (accessPredConstr a_0 m_1)))
            ))
        (pop)

        ; invariant 0 <= white && white <= unsorted && unsorted <= blue && blue <= len(a)
        (push)
            (assert (not 
                (and (<= 0 white_1) (<= white_1 unsorted_2) (<= unsorted_2 blue_1) (<= blue_1 (len a_0)))
            ))
        (pop)

        ; invariant forall i: Int :: 0 <= i && i < len(a) ==> m[i] == 0 || m[i] == 1 || m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i (len a_0))) 
                    (or 
                        (= 0 (select m_1 i))
                        (= 1 (select m_1 i))
                        (= 2 (select m_1 i))
                    )
                ))
            ))
        (pop)

        ; invariant forall i : Int :: 0 <= i && i < white ==> m[i] == 0
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i white_1)) (= 0 (select m_1 i))))
            ))
        (pop)

        ; invariant forall i : Int :: white <= i && i < unsorted ==> m[i] == 1
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= white_1 i) (< i unsorted_2)) (= 1 (select m_1 i))))
            ))
        (pop)

        ; invariant forall i : Int :: blue <= i && i < len(a) ==> m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= blue_1 i) (< i (len a_0))) (= 2 (select m_1 i))))
            ))
        (pop)
    (pop)

    ; else if (tmp == 0)
    (push)
        (assert (= 0 tmp_0))

        ; loc(a,unsorted).value := loc(a,white).value;

        ; checking permission
        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_1 (loc a_0 white_1)) (FracChunkConstr val perm)) (> perm 0)))
            ))
            (check-sat)
        (pop)

        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_1 (loc a_0 unsorted_1)) (FracChunkConstr val perm)) (= perm 1)))
            ))
            (check-sat)
        (pop)

        (declare-const valueOwnHeap_2 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_2))
        (assert (= (select valueOwnHeap_2 (loc a_0 unsorted_1)) (FracChunkConstr (Val (select valueOwnHeap_1 (loc a_0 white_1))) 1)))
        (assert (forall ((index Loc)) (=> (not (= index (loc a_0 unsorted_1))) (= (select valueOwnHeap_1 index) (select valueOwnHeap_2 index)))))

        ; m[unsorted] := loc(a,white).value;
        (declare-const m_2 (Array Int Int))
        (assert (= (select m_2 unsorted_1) (Val (select valueOwnHeap_2 (loc a_0 white_1)))))
        (assert (forall ((i Int)) (=> (not (= i unsorted_1)) (= (select m_2 i) (select m_1 i)))))

        ; loc(a,white).value := tmp;
        ; checking permission
        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_2 (loc a_0 white_1)) (FracChunkConstr val perm)) (= perm 1)))
            ))
            (check-sat)
        (pop)

        (declare-const valueOwnHeap_3 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_3))
        (assert (= (select valueOwnHeap_3 (loc a_0 white_1)) (FracChunkConstr tmp_0 1)))
        (assert (forall ((index Loc)) (=> (not (= index (loc a_0 white_1))) (= (select valueOwnHeap_2 index) (select valueOwnHeap_3 index)))))

        ; m[white] := tmp;
        (declare-const m_3 (Array Int Int))
        (assert (= (select m_3 white_1) tmp_0))
        (assert (forall ((i Int)) (=> (not (= i white_1)) (= (select m_3 i) (select m_2 i)))))

        ; white := white + 1;
        (declare-const white_2 Int)
        (assert (= white_2 (+ white_1 1)))

        ; unsorted := unsorted + 1;
        (declare-const unsorted_2 Int)
        (assert (= unsorted_2 (+ unsorted_1 1)))

        ; fold access(a, m)

        ; checking permission
        (push)
            (assert (not 
                (forall ((i Int)) 
                    (=> 
                        (and (<= 0 i) (< i (len a_0))) 
                        (= (select valueOwnHeap_3 (loc a_0 i)) (FracChunkConstr (select m_3 i) 1))    
                    )
                )
            ))
            (check-sat)
        (pop)

        (declare-const accessPredHeap_5 accessPredHeap)
        (assert (= (+ (select accessPredHeap_4 (accessPredConstr a_0 m_3)) 1)(select accessPredHeap_5 (accessPredConstr a_0 m_3))))

        (assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_3))) (= (select accessPredHeap_4 index) (select accessPredHeap_5 index)))))

        (declare-const valueOwnHeap_4 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_4))
        (assert (forall ((i Int)) 
            (=> 
                (and (<= 0 i) (< i (len a_0)))
                (= (IntFracChunkSubtract (select valueOwnHeap_3 (loc a_0 i)) (FracChunkConstr (select m_3 i) 1)) (select valueOwnHeap_4 (loc a_0 i)))
            )
        ))

        (assert (forall ((index Loc)) 
            (or 
                (exists ((i Int)) (and (<= 0 i) (< i (len a_0)) (= index (loc a_0 i))))
                (= (select valueOwnHeap_3 index) (select valueOwnHeap_4 index))
            )
        ))


        ; re-establishing Invariants

        ; invariant access(a, m)
        (push)
            (assert (not 
                (<= 1 (select accessPredHeap_5 (accessPredConstr a_0 m_3)))
            ))
            (check-sat)
        (pop)

        ; invariant 0 <= white && white <= unsorted && unsorted <= blue && blue <= len(a)
        (push)
            (assert (not 
                (and (<= 0 white_2) (<= white_2 unsorted_2) (<= unsorted_2 blue_1) (<= blue_1 (len a_0)))
            ))
            (check-sat)
        (pop)

        ; invariant forall i: Int :: 0 <= i && i < len(a) ==> m[i] == 0 || m[i] == 1 || m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i (len a_0))) 
                    (or 
                        (= 0 (select m_3 i))
                        (= 1 (select m_3 i))
                        (= 2 (select m_3 i))
                    )
                ))
            ))
        (pop)

        ; invariant forall i : Int :: 0 <= i && i < white ==> m[i] == 0
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i white_2)) (= 0 (select m_3 i))))
            ))
            (check-sat)
        (pop)

        ; invariant forall i : Int :: white <= i && i < unsorted ==> m[i] == 1
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= white_2 i) (< i unsorted_2)) (= 1 (select m_3 i))))
            ))
            (check-sat)
        (pop)

        ; invariant forall i : Int :: blue <= i && i < len(a) ==> m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= blue_1 i) (< i (len a_0))) (= 2 (select m_3 i))))
            ))
            (check-sat)
        (pop)
    (pop)

    ; else
    (push)
        (assert (and (not (= tmp_0 1)) (not (= tmp_0 0))))

        ; loc(a,unsorted).value := loc(a,blue - 1).value;

        ; checking permission
        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_1 (loc a_0 (- blue_1 1))) (FracChunkConstr val perm)) (> perm 0)))
            ))
            (check-sat)
        (pop)

        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_1 (loc a_0 unsorted_1)) (FracChunkConstr val perm)) (= perm 1)))
            ))
            (check-sat)
        (pop)

        (declare-const valueOwnHeap_2 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_2))
        (assert (= (select valueOwnHeap_2 (loc a_0 unsorted_1)) (FracChunkConstr (Val (select valueOwnHeap_1 (loc a_0 (- blue_1 1)))) 1)))
        (assert (forall ((index Loc)) (=> (not (= index (loc a_0 unsorted_1))) (= (select valueOwnHeap_1 index) (select valueOwnHeap_2 index)))))

        ; m[unsorted] := loc(a,blue - 1).value;
        (declare-const m_2 (Array Int Int))
        (assert (= (select m_2 unsorted_1) (Val (select valueOwnHeap_1 (loc a_0 (- blue_1 1))))))
        (assert (forall ((i Int)) (=> (not (= i unsorted_1)) (= (select m_2 i) (select m_1 i)))))

        ; blue := blue - 1;
        (declare-const blue_2 Int)
        (assert (= blue_2 (- blue_1 1)))

        ; loc(a,blue).value := tmp;
        ; checking permission
        (push)
            (assert (not 
                (exists ((val Int) (perm Real)) (and (= (select valueOwnHeap_2 (loc a_0 blue_2)) (FracChunkConstr val perm)) (= perm 1)))
            ))
            (check-sat)
        (pop)

        (declare-const valueOwnHeap_3 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_3))
        (assert (= (select valueOwnHeap_3 (loc a_0 blue_2)) (FracChunkConstr tmp_0 1)))
        (assert (forall ((index Loc)) (=> (not (= index (loc a_0 blue_2))) (= (select valueOwnHeap_2 index) (select valueOwnHeap_3 index)))))

        ; m[blue] = tmp;
        (declare-const m_3 (Array Int Int))
        (assert (= (select m_3 blue_2) tmp_0))
        (assert (forall ((i Int)) (=> (not (= i blue_2)) (= (select m_3 i) (select m_2 i)))))

        ; fold access(a, m)

        ; checking permission
        (push)
            (assert (not 
                (forall ((i Int)) 
                    (=> 
                        (and (<= 0 i) (< i (len a_0))) 
                        (= (select valueOwnHeap_3 (loc a_0 i)) (FracChunkConstr (select m_3 i) 1))    
                    )
                )
            ))
            (check-sat)
        (pop)

        (declare-const accessPredHeap_5 accessPredHeap)
        (assert (= (+ (select accessPredHeap_4 (accessPredConstr a_0 m_3)) 1)(select accessPredHeap_5 (accessPredConstr a_0 m_3))))

        (assert (forall ((index accessPred)) (=> (not (= index (accessPredConstr a_0 m_3))) (= (select accessPredHeap_4 index) (select accessPredHeap_5 index)))))

        (declare-const valueOwnHeap_4 (FracOwnHeap Int))
        (assert (IntHeapValid valueOwnHeap_4))
        (assert (forall ((i Int)) 
            (=> 
                (and (<= 0 i) (< i (len a_0)))
                (= (IntFracChunkSubtract (select valueOwnHeap_3 (loc a_0 i)) (FracChunkConstr (select m_3 i) 1)) (select valueOwnHeap_4 (loc a_0 i)))
            )
        ))

        (assert (forall ((index Loc)) 
            (or 
                (exists ((i Int)) (and (<= 0 i) (< i (len a_0)) (= index (loc a_0 i))))
                (= (select valueOwnHeap_3 index) (select valueOwnHeap_4 index))
            )
        ))

        ; re-establishing Invariants

        ; invariant access(a, m)
        (push)
            (assert (not 
                (<= 1 (select accessPredHeap_5 (accessPredConstr a_0 m_3)))
            ))
            (check-sat)
        (pop)

        ; invariant 0 <= white && white <= unsorted && unsorted <= blue && blue <= len(a)
        (push)
            (assert (not 
                (and (<= 0 white_1) (<= white_1 unsorted_1) (<= unsorted_1 blue_2) (<= blue_2 (len a_0)))
            ))
            (check-sat)
        (pop)

        ; invariant forall i: Int :: 0 <= i && i < len(a) ==> m[i] == 0 || m[i] == 1 || m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i (len a_0))) 
                    (or 
                        (= 0 (select m_3 i))
                        (= 1 (select m_3 i))
                        (= 2 (select m_3 i))
                    )
                ))
            ))
        (pop)

        ; invariant forall i : Int :: 0 <= i && i < white ==> m[i] == 0
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= 0 i) (< i white_1)) (= 0 (select m_3 i))))
            ))
            (check-sat)
        (pop)

        ; invariant forall i : Int :: white <= i && i < unsorted ==> m[i] == 1
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= white_1 i) (< i unsorted_1)) (= 1 (select m_3 i))))
            ))
            (check-sat)
        (pop)

        ; invariant forall i : Int :: blue <= i && i < len(a) ==> m[i] == 2
        (push)
            (assert (not 
                (forall ((i Int)) (=> (and (<= blue_2 i) (< i (len a_0))) (= 2 (select m_3 i))))
            ))
            (check-sat)
        (pop)
    (pop)
(pop)


; inhale negation of loop condition
(assert (not (< unsorted_1 blue_1)))

; establishing post-conditions

; ensures access(a,m)
(push)
    (assert (not 
        (<= 1 (select accessPredHeap_3 (accessPredConstr a_0 m_1)))
    ))
    (check-sat)
(pop)

; ensures forall i: Int, j: Int :: 0 <= i && i < j && j < len(a) ==> ordered(m,i,j)
(push)
    (assert (not
        (forall 
            ((i Int) (j Int)) 
            (=> 
                (and (<= 0 i) (< i j) (< j (len a_0))) 
                (or 
                    (<= 1 (select orderedPredHeap_0 (orderedPredConstr m_1 i j)))
                    (<= (select m_1 i) (select m_1 j))
                )
            )
        )
    ))

    (check-sat)
(pop)

(echo "SAT/Unknown:")
(check-sat)

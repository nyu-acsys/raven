(set-logic ALL)

(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :timeout 2000)

; A manual encoding of max() from array-max.rav

(declare-sort Loc 0)
(declare-sort Field 1)
; Fields to be separated by type

;(declare-datatype OwnHeapIndex (par (T) ((OwnIndex (Loc Loc) (Field (Field T))))))

(declare-datatype FracHeapChunk (par (T) ((FracHeapNull) (FracChunk (Val T) (Own Real)))))
; separate heaps for each RA, field

(declare-datatype HeapChunk (par (T) ((HeapNull) (Chunk (Val T)))))

(define-sort FracOwnHeap (T) (Array Loc (FracHeapChunk T)))
(define-sort OwnHeap (T) (Array Loc (HeapChunk T)))

;(declare-datatype Predicate (
;    (predNull)
;    (arr)
;    (is_max (is_maxArg1 Int) (is_maxArg2 (Array Int Int)) (is_maxArg3 Int))
;    (arr (arrArg1 ) (arrArg2 (Array Int Int)))
;))
; Would be better if didn't have to declare all constructors for Predicate up front.

; (declare-const PredHeap0 (Array Int Predicate))

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
            ((FracChunk i r) (and (<= 0 r) (>= 1 r)))            
        ))
	)
))

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
            ((FracChunk i r) (and (<= 0 r) (>= 1 r)))            
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

; field val: Int
(declare-const val (Field Int))

(declare-datatype Predicate (
    (predNull)
    (is_max (is_maxArg1 Int) (is_maxArg2 (Array Int Int)) (is_maxArg3 Int))
    (arr (arrArg1 IArray) (arrArg2 (Array Int Int)))
))
; Would be better if didn't have to declare all constructors for Predicate up front.

; ---------------------------------

(declare-const a IArray)
(declare-const m (Array Int Int))
(declare-const x Int)

(declare-const PredHeap11 (Array Int Predicate))
(declare-const PredHeap0 (Array Int Predicate))

; requires arr(a,m)
(assert (= PredHeap0 (store PredHeap0 0 (arr a m))))

; if (len(a) == 0)
(push)
    (assert (= (len a) 0))
    (declare-const x_1 Int)
    (assert (= x_1 -1))

    ; checking postconditions

    (push)
        (assert (not
            (= (arr a m) (select PredHeap0 0))))
        
        (check-sat)
    (pop)

    (push)
        (assert (not
            (ite (= (len a) 0) (= x_1 -1) (and (<= 0 x_1) (< x_1 (len a))))
        ))
        (check-sat)
    (pop)

    (push)
    ; fails -- manually unfolding and proving body of predicate in next request.
        (echo "What")
        (assert (not
            (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (is_max x m (len a)) (select PredHeap0 0))))
        ))
        (check-sat)
        ; this request times out. Why might that be?
    (pop)

    (push)
        (assert (not
            (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (<= (select m j) (select m x_1))))
        ))
        (check-sat)
    (pop)
(pop)

; else
(push)
    (assert (not (= (len a) 0)))

    (declare-const y Int)
    (declare-const x_1 Int)
    (assert (= x_1 0))
    (assert (= y (- (len a) 1)))

    ; while loop
    ; proving invariants before loop is executed
    (push)
        (assert (not
            (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap0 ii))))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (and (<= 0 x_1) (<= x_1 y) (< y (len a)))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (or 
                (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y i) (< i (len a)))) (< (select m i) (select m x_1))))
                (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y i) (< i (len a)))) (< (select m i) (select m y))))
            )
        ))
        (check-sat)
    (pop)

    ; checking properties of while loop
    (push)
        ; executing an iteration of loop
        (assert (not (= x_1 y)))

        ; unfold arr(a,m)
        ; checking ownership
        (push)
            (assert (not
                (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap0 ii))))
            ))
            (check-sat)
        (pop)

        (declare-const ii_0 Int)
        (assert (and (<= 0 ii_0) (<= ii_0 0) (= (arr a m) (select PredHeap0 ii_0))))

        (declare-const PredHeap1 (Array Int Predicate))
        (assert (= PredHeap1 (store PredHeap0 ii_0 predNull)))

        (declare-const valHeap (FracOwnHeap Int))

        (assert (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (= valHeap (store valHeap (loc a j) (FracChunk (select m j) 1) )))))
        ; handling quantified permissions by encoding to SAT directly. One question is what to do if the quantified permissions only contain some of the permissions for a specific location?

        ;(echo "Should be SAT/unknown:")
        ;(check-sat)

        ; if (loc(a, x).val <= loc(a, y).val)
        (push)
            (assert (<= (Val (select valHeap (loc a x_1))) (Val (select valHeap (loc a y)))))

            (declare-const x_2 Int)
            (assert (= x_2 (+ x_1 1)))

            ; fold arr(a,m)
            ; checking ownership
            (push)
                (assert (not (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (= valHeap (store valHeap (loc a j) (FracChunk (select m j) 1) ))))))
                (check-sat)
            (pop)

            (declare-const valHeap1 (FracOwnHeap Int))
            (assert (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (= (select valHeap1 (loc a j) ) (as FracHeapNull (FracHeapChunk Int)) ))))

            (assert (forall ((j Int)) (=> (not (and (<= 0 j) (< j (len a)))) (= (select valHeap1 (loc a j)) (select valHeap (loc a j)) ))))

            ;(echo "Should be SAT/unknown:")
            ;(check-sat)

            (declare-const PredHeap2 (Array Int Predicate))
            (assert (= PredHeap2 (store PredHeap1 0 (arr a m))))

            ; re-establishing invariants

            (push)
                (assert (not
                    (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap2 ii))))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (and (<= 0 x_2) (<= x_2 y) (< y (len a)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (or 
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y i) (< i (len a)))) (< (select m i) (select m x_2))))
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y i) (< i (len a)))) (< (select m i) (select m y))))
                    )
                ))
                (echo "Why")
                (check-sat)
            (pop)
        (pop)

        ; else
        (push)
            (assert (not (<= (Val (select valHeap (loc a x_1))) (Val (select valHeap (loc a y))))))

            (declare-const y_1 Int)
            (assert (= y_1 (- y 1)))

            ; fold arr(a,m)
            ; checking ownership
            (push)
                (assert (not (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (= valHeap (store valHeap (loc a j) (FracChunk (select m j) 1) ))))))
                (check-sat)
            (pop)

            (declare-const valHeap1 (FracOwnHeap Int))
            (assert (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (= valHeap1 (store valHeap (loc a j) (as FracHeapNull (FracHeapChunk Int)) )))))

            ;(echo "Should be SAT/unknown:")
            ;(check-sat)

            (declare-const PredHeap2 (Array Int Predicate))
            (assert (= PredHeap2 (store PredHeap1 0 (arr a m))))

            ; re-establishing invariants

            (push)
                (assert (not
                    (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap2 ii))))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (and (<= 0 x_1) (<= x_1 y_1) (< y_1 (len a)))
                ))
                (check-sat)
            (pop)

            (push)
                (assert (not
                    (or 
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y_1 i) (< i (len a)))) (< (select m i) (select m x_1))))
                        (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_1)) (and (< y_1 i) (< i (len a)))) (< (select m i) (select m y_1))))
                    )
                ))
                (check-sat)
            (pop)
        (pop)
    (pop)

    ; abstracting over while loop
    ; which variables to declare new? For example what to do with PredHeap etc?
    (declare-const x_2 Int)
    (declare-const y_1 Int)

    (assert (= x_2 y_1))
    
    (assert
        (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap0 ii))))
    )

    (assert 
        (and (<= 0 x_2) (<= x_2 y_1) (< y_1 (len a)))
    )

    (assert 
        (or 
            (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a)))) (< (select m i) (select m x_2))))
            (forall ((i Int)) (=> (or (and (<= 0 i) (< i x_2)) (and (< y_1 i) (< i (len a)))) (< (select m i) (select m y_1))))
        )
    )

    ; checking postconditions

    (push)
        (assert (not
            (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (arr a m) (select PredHeap0 ii))))
        ))
        (check-sat)
    (pop)

    (push)
        (assert (not
            (ite (= (len a) 0) (= x_2 -1) (and (<= 0 x_2) (< x_2 (len a))))
        ))
        (check-sat)
    (pop)

    (push)
    ; fails -- manually unfolding and proving body of predicate in next request.
        (assert (not
            (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (is_max x_2 m (len a)) (select PredHeap0 ii))))
        ))
        ;(check-sat)
        ; this request times out. Why might that be?
    (pop)

    (push)
        (assert (not
            (forall ((j Int)) (=> (and (<= 0 j) (< j (len a))) (<= (select m j) (select m x_2))))
        ))
        (check-sat)
    (pop)

(pop)

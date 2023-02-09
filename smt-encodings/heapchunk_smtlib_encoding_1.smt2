(set-logic UFLRA)

(declare-sort Loc)
(declare-sort HeapChunk)
(declare-sort HeapIndex)

(declare-sort Array)

(declare-fun select (Array HeapIndex) HeapChunk)
(declare-fun store (Array HeapIndex HeapChunk) Array)

(assert (forall ((a (Array)) (i HeapIndex) (e HeapChunk))
	(= (select (store a i e) i) e)) )

(assert (forall ((a (Array)) (i HeapIndex) (j HeapIndex) (e HeapChunk))
      (=> (distinct i j)
               (= (select (store a i e) j) (select a j)))))

(assert (forall ((a (Array)) (b (Array)))
      (=> (forall ((i HeapIndex)) (= (select a i) (select b i)))
               (= a b))))


(declare-fun makeHeapChunk (Loc Real) (HeapChunk))
(declare-fun valid (Array) Bool)

(declare-const empty Array)

(assert (
	forall (
		(heap Array)
		(i1 HeapIndex) 
		(i2 HeapIndex) 
		(l1 Loc) 
		(l2 Loc) 
		(own_val1 Real) 
		(own_val2 Real)
	)

	(=> 
		(and
			(valid heap)
			(= (select heap i1) (makeHeapChunk l1 own_val1)) 
			(= (select heap i2) (makeHeapChunk l2 own_val2)) 
			(> (+ own_val1 own_val2) 1)
			(not (= i1 i2))
		)

		(not (= l1 l2))
	)
))



(declare-const index0 HeapIndex)
(declare-const index1 HeapIndex)
;(assert (not (= index0 index1))) ; commenting out this line makes it work

(declare-const l1 Loc)

(declare-const heap0 Array)
(assert (valid heap0))

(assert (= heap0 (store empty index0 (makeHeapChunk l1 0.6))))

(declare-const heap1 Array)
(assert (valid heap1))
(assert (= heap1 (store heap0 index1 (makeHeapChunk l1 0.35))))


(check-sat)
(exit)
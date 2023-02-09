(set-logic AUFLIRA)
(set-option :produce-models true)

(set-option :macro-finder true)


(declare-sort Loc 0)
(declare-sort HeapChunk 0)
(declare-sort HeapIndex 0)

(declare-fun makeHeapChunk (Loc Real) HeapChunk)
(declare-fun valid ((Array HeapIndex HeapChunk)) Bool)

(declare-const empty (Array HeapIndex HeapChunk))

(assert (
	forall (
		(heap (Array HeapIndex HeapChunk))
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
(assert (distinct index0 index1)) ; commenting out this line makes it work

(declare-const l1 Loc)

(declare-const heap0 (Array HeapIndex HeapChunk))
(assert (valid heap0))

(assert (= heap0 (store empty index0 (makeHeapChunk l1 0.6))))

(declare-const heap1 (Array HeapIndex HeapChunk))
(assert (valid heap1))
(assert (= heap1 (store heap0 index1 (makeHeapChunk l1 0.5))))

(check-sat)
(get-model)
(exit)
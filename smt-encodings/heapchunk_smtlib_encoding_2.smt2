; (set-logic AUFLIRA)
(set-option :produce-models true)
; (set-option :macro-finder true)

(declare-sort Loc 0)
; (declare-sort HeapChunk 0)
(declare-sort HeapIndex 0)	

(declare-datatypes ((HeapChunk 0)) (((FracChunk (Loc Loc) (Own Real)))))

(declare-fun valid ((Array HeapIndex HeapChunk)) Bool)

(declare-const empty (Array HeapIndex HeapChunk))


(declare-const heap0 (Array HeapIndex HeapChunk))
(assert (valid heap0))

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
			; (= heap heap0)
			(= (select heap i1) (FracChunk l1 own_val1)) 
			(= (select heap i2) (FracChunk l2 own_val2)) 
			(> (+ own_val1 own_val2) 1)
			(not (= i1 i2))
		)

		(not (= l1 l2))
	)
))



(declare-const index0 HeapIndex)
(declare-const index1 HeapIndex)
(declare-const index2 HeapIndex)
(declare-const index3 HeapIndex)
(declare-const index4 HeapIndex)
(assert (distinct index0 index1 index2 index3 index4))

(declare-const l1 Loc)
(declare-const l2 Loc)
(declare-const l3 Loc)
(declare-const l4 Loc)
(declare-const l5 Loc)
(assert (distinct l1 l2))

(assert (= heap0 (store heap0 index0 (FracChunk l1 0.6))))
(assert (= heap0 (store heap0 index1 (FracChunk l2 0.1))))
(assert (= heap0 (store heap0 index2 (FracChunk l1 0.3))))

(check-sat)
; (get-model)
(exit)
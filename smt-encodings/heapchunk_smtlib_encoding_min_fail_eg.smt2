(set-logic AUFLIRA)

(declare-sort Loc)

(declare-sort HeapChunk)

(declare-fun makeHeapChunk (Loc Real) (HeapChunk))

; Declare an array "heap" with index type "Int" and element type "HeapChunk"
(declare-fun heap (Int) (Array Int HeapChunk))

(declare-const l1 Loc)

(assert (= (heap 1) (store (heap 0) 0 (makeHeapChunk l1 0.5))))


(assert (forall ((t Int) (i1 Int) (i2 Int) (l1 Loc) (l2 Loc) (own_val1 Real) (own_val2 Real)) 
	(=> (and (and (and (= (select (heap t) i1) (makeHeapChunk l1 own_val1)) (= (select (heap t) i2) (makeHeapChunk l2 own_val2))) (> (+ own_val1 own_val2) 1)) (not (= i1 i2))) (not (= l1 l2)))) 
)



(check-sat)
(exit)
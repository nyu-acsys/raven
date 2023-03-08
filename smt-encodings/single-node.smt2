(set-logic ALL)

(set-option :produce-models true)
(set-option :produce-unsat-cores true)

; A manual encoding of acquire() method from single-node.rav

(declare-sort Loc 0)
(declare-sort Field 0)

(declare-datatype FracHeapChunk (par (T) ((FracNull) (FracChunk (Val T) (Own Real)))))
; separate heaps for each RA, field


(declare-datatype Option (par (T) ( (none) (some (val T) ))))
(declare-sort MethodName 0)
(declare-sort AtomicUpdID 0)

(declare-datatype AUHeapChunk (
	(AUNull) 
	(AUChunk (id AtomicUpdID) (name MethodName) (param1 Loc) (comm Bool) (open (Option Bool)))
))	

(define-sort FracHeap (T) (Array Loc (FracHeapChunk T)))
(declare-const AUHeap (Array Int AUHeapChunk))

(declare-fun BoolHeapValid ((FracHeap Bool)) Bool)
(assert (
	forall (
		(heap (FracHeap Bool))
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
(declare-const acqID (AtomicUpdID))
(declare-const acquire (MethodName))
(declare-const l Loc)

(declare-const acqAU0 (AUHeapChunk))
(assert (= acqAU0 (AUChunk acqID acquire l false none)))

; add acquireAU to the heap
(declare-const AUHeap0 (Array Int AUHeapChunk))
(assert (= AUHeap0 (store AUHeap0 0 acqAU0)))

;val phi: Perm;
(declare-const phi (AtomicUpdID))

;phi := bindAU();
(assert (= phi (id (select AUHeap 0))))
; Fix 0 as special location for bindAU?

;val b: Bool;
(declare-const b0 Bool)

;b := openAU(phi);
(declare-const acqAU1 (AUHeapChunk))
(assert (= acqAU1 (AUChunk acqID acquire l false (some b0))))
; remove AU from the heap
(declare-const AUHeap1 (Array Int AUHeapChunk))
(assert (= AUHeap1 (store AUHeap0 0 acqAU1)))

; add pre to FracHeap
(declare-const FracHeap0 (FracHeap Bool))
(assert (= FracHeap0 (store FracHeap0 l (FracChunk b0 1))))






(check-sat)
(set-logic ALL)
; (set-option :produce-models true)
; (set-option :smt.mbqi false)

(declare-sort Loc 0)
(declare-datatype
                   FracHeapChunk (par (T) ( (FracHeapNull)
                   (FracChunkConstr (FracVal T) (FracOwn Real))
                   (FracHeapTop))))
(define-sort FracHeap (T) (Array Loc (FracHeapChunk T)))
(define-sort PredHeap (T) (Array T Int))


(declare-sort K 0)
(declare-sort Node 0)

(declare-sort $Set 1)
(declare-fun $select (($Set K) K) Bool)
(declare-fun $select (($Set Int)) Bool)

(declare-sort $Map 2)


(declare-fun IntFracHeapValid ((FracHeap Int)) Bool)
(assert
        (forall
                ((heap (FracHeap Int)) (l Loc)
                 (chunk (FracHeapChunk Int)))
                (=> (and (IntFracHeapValid heap) (= (select heap l) chunk))
                   (match chunk ((FracHeapNull true) ((FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) (FracHeapTop false) )))))

(define-fun Set_K_FracChunkAdd ((x1 (FracHeapChunk ($Set K))) (x2 (FracHeapChunk ($Set K)))) (FracHeapChunk ($Set K)) 
    (match x1 (
        (FracHeapNull x2)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull x1)
            ((FracChunkConstr v2 r2) (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2)) (as FracHeapTop (FracHeapChunk ($Set K)))))
            (FracHeapTop (as FracHeapTop (FracHeapChunk ($Set K))))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk ($Set K))))
    ))
)

(define-fun Set_K_FracChunkSubtract ((x1 (FracHeapChunk ($Set K))) (x2 (FracHeapChunk ($Set K)))) (FracHeapChunk ($Set K)) 
    (match x2 (
        (FracHeapNull x1)
        ((FracChunkConstr v2 r2) (match x1 (
            (FracHeapNull (as FracHeapTop (FracHeapChunk ($Set K))))
            ((FracChunkConstr v1 r1) 
                (ite (= v1 v2) 
                    (ite (= r1 r2) 
                        (as FracHeapNull (FracHeapChunk ($Set K)))
                        (ite (> r1 r2) 
                            (FracChunkConstr v1 (- r1 r2))
                            (as FracHeapTop (FracHeapChunk ($Set K)))        
                        )
                    ) 
                    (as FracHeapTop (FracHeapChunk ($Set K)))
                )
            )
            (FracHeapTop (as FracHeapTop (FracHeapChunk ($Set K))))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk ($Set K))))
    ))
)

(declare-fun Set_K_HeapValid ((FracHeap ($Set K))) Bool)
(assert (
	forall (
		(heap (FracHeap ($Set K)))
		(l Loc)
		(chunk (FracHeapChunk ($Set K)))
	)

	(=> 
		(and
			(Set_K_HeapValid heap)
			(= (select heap l) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunkConstr i r) (and (<= 0 r) (>= 1 r)))
            (FracHeapTop false)
        ))
	)
))

(define-fun Set_K_HeapChunkCompare ((x1 (FracHeapChunk ($Set K)))
            (x2 (FracHeapChunk ($Set K)))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))

(declare-sort FlowInt 0)
(declare-fun dom (FlowInt) ($Set Node))

(declare-fun $select (($Set Node) Node) Bool)
(declare-fun $select (($Map Node Bool) Node) Bool)
(declare-fun $select (($Map Node FlowInt) Node) FlowInt)
(declare-fun $select (($Map Node ($Set K)) Node) ($Set K))

(declare-const r@0 Loc)
(declare-const C@1 ($Set K))
; (declare-const C@1 Int) 

(declare-const rpOwnHeap@0 (FracHeap ($Set K)))
(assert (Set_K_HeapValid rpOwnHeap@0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk ($Set K))) (select rpOwnHeap@0 index))))


(declare-const rpOwnHeap@1 (FracHeap ($Set K)))
(assert (Set_K_HeapValid rpOwnHeap@1))

(assert (= (select rpOwnHeap@1 r@0) (FracChunkConstr C@1 (/ 1 2))))
(assert (forall ((l Loc)) 
    (=>
        (not (= l r@0))
        (= (select rpOwnHeap@1 l) (select rpOwnHeap@0 l))
    ) 
))

; (check-sat)

(push)
    (assert (not (
        exists (
            ; (m_lk@1 (Array Node Bool)) (m_In@1 (Array Node FlowInt)) (m_Cn@1 (Array Node (Set K))) (I@1 FlowInt) 
            (C@2 ($Set K)) 
            ; (n@1 Node)
        )

            ; (and
                (= (FracChunkConstr C@2 (/ 1 2)) (select rpOwnHeap@1 r@0))

            ; )
    )))
    (check-sat)
    ; (get-model)
(pop)


; -----------------------


(declare-datatype nodeRPred ((nodeRPredConstr (nodeRPredArg1 Node) (nodeRPredArg2 Bool) (nodeRPredArg3 FlowInt) (nodeRPredArg4 ($Set K)))))

(declare-const nodeRPredHeap@0 (PredHeap nodeRPred))
(assert (forall ((index nodeRPred)) (= 0 (select nodeRPredHeap@0 index))))

(declare-const m_lk@0 ($Map Node Bool))
(declare-const m_In@0 ($Map Node FlowInt))
(declare-const m_Cn@0 ($Map Node ($Set K)))
(declare-const I@0 FlowInt)
; (declare-const C@1 ($Set K))
(declare-const n@0 Node)

(declare-const nodeRPredHeap@1 (PredHeap nodeRPred))
(assert (forall ((n Node))
    (=> ($select (dom I@0) n)
        (= (select nodeRPredHeap@1 (nodeRPredConstr n (select m_lk@0 n) (select m_In@0 n) (select m_Cn@0 n))) (+ 1 (select nodeRPredHeap@0 (nodeRPredConstr n (select m_lk@0 n) (select m_In@0 n) (select m_Cn@0 n)))))
    )
))

; check permission
(push)
    (assert (not (
        exists (
            (m_lk@1 ($Map Node Bool)) (m_In@1 ($Map Node FlowInt)) (m_Cn@1 ($Map Node ($Set K))) (I@1 FlowInt) 
            (C@2 ($Set K)) 
            (n@1 Node)
        )
            (and
                (forall ((n1 Node)) 
                    (=> ($select (dom I@1) n1)
                        (< 0 (select nodeRPredHeap@1 (nodeRPredConstr n1 (select m_lk@1 n1) (select m_In@1 n1) (select m_Cn@1 n1))))
                    )
                )
            )
    )))
    (check-sat)
    ; (get-model)
(pop)
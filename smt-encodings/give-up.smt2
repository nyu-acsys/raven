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

(define-fun LocFracChunkAdd ((x1 (FracHeapChunk Loc)) (x2 (FracHeapChunk Loc))) (FracHeapChunk Loc) 
    (match x1 (
        (FracHeapNull x2)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull x1)
            ((FracChunkConstr v2 r2) (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2)) (as FracHeapTop (FracHeapChunk Loc))))
            (FracHeapTop (as FracHeapTop (FracHeapChunk Loc)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Loc)))
    ))
)

(define-fun LocFracChunkSubtract ((x1 (FracHeapChunk Loc)) (x2 (FracHeapChunk Loc))) (FracHeapChunk Loc) 
    (match x2 (
        (FracHeapNull x1)
        ((FracChunkConstr v2 r2) (match x1 (
            (FracHeapNull (as FracHeapTop (FracHeapChunk Loc)))
            ((FracChunkConstr v1 r1) 
                (ite (= v1 v2) 
                    (ite (= r1 r2) 
                        (as FracHeapNull (FracHeapChunk Loc))
                        (ite (> r1 r2) 
                            (FracChunkConstr v1 (- r1 r2))
                            (as FracHeapTop (FracHeapChunk Loc))        
                        )
                    ) 
                    (as FracHeapTop (FracHeapChunk Loc))
                )
            )
            (FracHeapTop (as FracHeapTop (FracHeapChunk Loc)))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk Loc)))
    ))
)

(declare-fun LocHeapValid ((FracOwnHeap Loc)) Bool)
(assert (
	forall (
		(heap (FracOwnHeap Loc))
		(l Loc)
		(chunk (FracHeapChunk Loc))
	)

	(=> 
		(and
			(LocHeapValid heap)
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
; module GiveUpTemplate[K: Keyspace
(declare-sort K 0)
(declare-const KS (Set K))

; , Node: NodeImpl[K]]

(declare-datatype Op ((searchOp) (insertOp) (deleteOp)))

(declare-datatype opSpecPred ((opSpecPredConstr (opSpecPredArg1 Op) (opSpecPredArg2 K) (opSpecPredArg3 (Set K)) (opSpecPredArg4 (Set K)) (opSpecPredArg5 Bool))))

(declare-sort FlowInt)

(declare-sort Node)

(declare-fun dom (FlowInt) (Set Node))

(declare-datatype nodeRPred ((nodeRPredConstr (nodeRPredArg1 Node) (nodeRPredArg2 Bool) (nodeRPredArg3 FlowInt) (nodeRPredArg4 (Set K)))))

; pred nodePred
(declare-datatype nodePredPred ((nodePredPredConstr (nodePredPredArg1 Loc) (nodePredPredArg2 Node) (nodePredPredArg3 FlowInt) (nodePredPredArg4 (Set K)))))

; pred cssR
(declare-datatype cssRPred ((cssRPredConstr (cssRPredArg1 Loc) (cssRPredArg2 (Set K)))))

; pred globalinv
(declare-datatype globalinvPred ((globalinvPredConstr (globalinvPredArg1 Loc) (globalinvPredArg2 FlowInt))))

; pred globalRes
(declare-datatype globalResPred ((globalResPredConstr (globalResPredArg1 Loc) (globalResPredArg2 FlowInt) (globalResPredArg3 (Set K)))))

; inv cssI
(declare-datatype cssIPred ((cssIPredConstr (cssIPredArg1 Loc))))

(define-fun Set_K_FracChunkAdd ((x1 (FracHeapChunk (Set K))) (x2 (FracHeapChunk (Set K)))) (FracHeapChunk (Set K)) 
    (match x1 (
        (FracHeapNull x2)
        ((FracChunkConstr v1 r1) (match x2 (
            (FracHeapNull x1)
            ((FracChunkConstr v2 r2) (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2)) (as FracHeapTop (FracHeapChunk (Set K)))))
            (FracHeapTop (as FracHeapTop (FracHeapChunk (Set K))))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk (Set K))))
    ))
)

(define-fun Set_K_FracChunkSubtract ((x1 (FracHeapChunk (Set K))) (x2 (FracHeapChunk (Set K)))) (FracHeapChunk (Set K)) 
    (match x2 (
        (FracHeapNull x1)
        ((FracChunkConstr v2 r2) (match x1 (
            (FracHeapNull (as FracHeapTop (FracHeapChunk (Set K))))
            ((FracChunkConstr v1 r1) 
                (ite (= v1 v2) 
                    (ite (= r1 r2) 
                        (as FracHeapNull (FracHeapChunk (Set K)))
                        (ite (> r1 r2) 
                            (FracChunkConstr v1 (- r1 r2))
                            (as FracHeapTop (FracHeapChunk (Set K)))        
                        )
                    ) 
                    (as FracHeapTop (FracHeapChunk (Set K)))
                )
            )
            (FracHeapTop (as FracHeapTop (FracHeapChunk (Set K))))
        )))
        (FracHeapTop (as FracHeapTop (FracHeapChunk (Set K))))
    ))
)

(declare-fun Set_K_HeapValid ((FracOwnHeap (Set K))) Bool)
(assert (
	forall (
		(heap (FracOwnHeap (Set K)))
		(l Loc)
		(chunk (FracHeapChunk (Set K)))
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



; proc cssOp(r: Ref, ghost C: Set[K], dop: Op, k: K)
(declare-const r@0 Loc)
(declare-const C@0 (Set K))
(declare-const dop@0 Op)
(declare-const k@0 K)

(declare-const cssIPredHeap@0 (PredHeap cssIPred))
(assert (forall ((index cssIPred)) (= 0 (select cssIPredHeap@0 index))))

(declare-const cssRPredHeap@0 (PredHeap cssRPred))
(assert (forall ((index cssRPred)) (= 0 (select cssRPredHeap@0 index))))

(declare-const globalResPredHeap@0 (PredHeap globalResPred))
(assert (forall ((index globalResPred)) (= 0 (select globalResPredHeap@0 index))))

(declare-const nodeRPredHeap@0 (PredHeap nodeRPred))
(assert (forall ((index nodeRPred)) (= 0 (select nodeRPredHeap@0 index))))

(declare-const nodePredPredHeap@0 (PredHeap nodePredPred))
(assert (forall ((index nodePredPred)) (= 0 (select nodePredPredHeap@0 index))))

(declare-const nodeOwnHeap@0 (FracOwnHeap Loc))
(assert (LocHeapValid nodeOwnHeap@0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk Loc)) (select nodeOwnHeap@0 index))))

(declare-const rpOwnHeap@0 (FracOwnHeap (Set K)))
(assert (Set_K_HeapValid rpOwnHeap@0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk (Set K))) (select rpOwnHeap@0 index))))

; requires k in KS
(assert (select KS k@0))

; requires cssI(r)
(declare-const cssIPredHeap@1 (PredHeap cssIPred))
(assert (= 1 (select cssIPredHeap@1 (cssIPredConstr r@0))))
(assert (forall ((index cssIPred)) 
    (or 
        (= index (cssIPredConstr r@0)) 
        (= (select cssIPredHeap@0 index) (select cssIPredHeap@1 index))
    )
))

; atomic requires cssR(r,C)
(declare-const cssRPredHeap@1 (PredHeap cssRPred))
(assert (= 1 (select cssRPredHeap@1 (cssRPredConstr r@0 C@0))))
(assert (forall ((index cssRPred)) 
    (or
        (= index (cssRPredConstr r@0 C@0))
        (= (select cssRPredHeap@0 index) (select cssRPredHeap@1 index))
    )
))

; unfold cssI(r)
(declare-const cssRPredHeap@2 (PredHeap cssRPred))
(assert (= (- (select cssRPredHeap@2 (cssRPredConstr r@0 C@0)) 1) (select cssRPredHeap@2 (cssRPredConstr r@0 C@0))))
(assert (forall ((index cssRPred)) 
    (or
        (= index (cssRPredConstr r@0 C@0))
        (= (select cssRPredHeap@1 index) (select cssRPredHeap@2 index))
    )
))

(declare-const rpOwnHeap@1 (FracOwnHeap (Set K)))
(assert (Set_K_HeapValid rpOwnHeap@1))

(declare-const globalResPredHeap@1 (PredHeap globalResPred))

(declare-const nodeRPredHeap@1 (PredHeap nodeRPred))

(declare-const nodePredPredHeap@1 (PredHeap nodePredPred))

(assert (exists ((I FlowInt) (C (Set K)))
    (and
        (and 
            (= (Set_K_FracChunkAdd (select rpOwnHeap@0 r@0) (FracChunkConstr C 0.5)) (select rpOwnHeap@1 r@0))

            (forall ((l Loc)) 
                (or 
                    (= l r@0)
                    (= (select rpOwnHeap@0 r@0) (select rpOwnHeap@1 r@0))
                )
            )
        )

        (and
            (= (+ (select globalResPredHeap@0 (globalResPredConstr r@0 I C)) 1) (select globalResPredHeap@1 (globalResPredConstr r@0 I C)))

            (forall ((index globalResPred))
                (or
                    (= index (globalResPredConstr r@0 I C))
                    (= (select globalResPredHeap@0 index) (select globalResPredHeap@1 index))
                )
            )
        )

        (forall ((n Node))
            (ite (select (dom I) n)
                (exists 
                    ((lk Bool) (In FlowInt) (Cn (Set K)))
                    (and
                        (and 
                            (= (+ (select nodeRPredHeap@0 (nodeRPredConstr n lk In Cn)) 1) (select nodeRPredHeap@1 (nodeRPredConstr n lk In Cn)))

                            (forall ((lk2 Bool) (In2 FlowInt) (Cn2 (Set K))) 
                                (or
                                    (and (= lk2 lk) (= In2 In) (= Cn2 Cn))
                                    (= (select nodeRPredHeap@0 (nodeRPredConstr n lk2 In2 Cn2)) (select nodeRPredHeap@1 (nodeRPredConstr n lk2 In2 Cn2)))
                                )
                            )
                        )

                        (ite lk
                            (and
                                (= (+ (select nodePredPredHeap@0 (nodePredPredConstr r@0 n In Cn)) 1) (select nodePredPredHeap@1 (nodePredPredConstr r@0 n In Cn)))

                                (forall ((In2 FlowInt) (Cn2 (Set K))) 
                                    (or 
                                        (and (= In In2) (= Cn Cn2))

                                        (= (select nodePredPredHeap@0 (nodePredPredConstr r@0 n In2 Cn2)) (select nodePredPredHeap@1 (nodePredPredConstr r@0 n In2 Cn2)))
                                    )
                                )
                            )

                            (forall ((In2 FlowInt) (Cn2 (Set K)))
                                (= (select nodePredPredHeap@0 (nodePredPredConstr r@0 n In2 Cn2)) (select nodePredPredHeap@1 (nodePredPredConstr r@0 n In2 Cn2)))
                            )
                        )
                    )

                    
                )

                (and
                    (forall ((lk Bool) (In FlowInt) (Cn (Set K)))
                        (= (select nodeRPredHeap@0 (nodeRPredConstr n lk In Cn)) (select nodeRPredHeap@1 (nodeRPredConstr n lk In Cn)))
                    )

                    (forall ((In FlowInt) (Cn (Set K)))
                        (= (select nodePredPredHeap@0 (nodePredPredConstr r@0 n In Cn)) (select nodePredPredHeap@1 (nodePredPredConstr r@0 n In Cn)))
                    )
                )
            )
        )  
    )
))

(assert (forall ((r Loc))
    (or 
        (= r r@0)
        (forall ((n Node) (In FlowInt) (Cn (Set K)))
            (= (select nodePredPredHeap@0 (nodePredPredConstr r n In Cn)) (select nodePredPredHeap@1 (nodePredPredConstr r n In Cn)))
        )
    )
))


; var n := traverse(r, r.node, k)
; How do we have permission over r.node?
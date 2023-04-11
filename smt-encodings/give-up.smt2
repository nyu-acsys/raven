(set-logic ALL)

(set-option :produce-models true)
(set-option :smt.mbqi false)
; (set-option :produce-unsat-cores true)
(set-option :timeout 2000)

; A manual encoding of max() from array-max.rav



(declare-sort Loc 0)
(declare-datatype
                   FracHeapChunk (par (T) ( (FracHeapNull)
                   (FracChunkConstr (FracVal T) (FracOwn Real))
                   (FracHeapTop))))
(define-sort FracHeap (T) (Array Loc (FracHeapChunk T)))
(define-sort PredHeap (T) (Array T Int))
(declare-fun IntFracHeapValid ((FracHeap Int)) Bool)
(assert
        (forall
                ((heap (FracHeap Int)) (l Loc)
                 (chunk (FracHeapChunk Int)))
                (=> (and (IntFracHeapValid heap) (= (select heap l) chunk))
                   (match chunk ((FracHeapNull true) ((FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) (FracHeapTop false) )))))
(define-fun IntFracChunkAdd ((x1 (FracHeapChunk Int))
            (x2 (FracHeapChunk Int))) (FracHeapChunk Int)
             (match x1 ((FracHeapNull x2) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2))
              (as FracHeapTop (FracHeapChunk Int)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Int))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Int))) )))
(define-fun IntFracChunkSubtract ((x1 (FracHeapChunk Int))
            (x2 (FracHeapChunk Int))) (FracHeapChunk Int)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
             (match x1 ((FracHeapNull
            (as FracHeapTop (FracHeapChunk Int))) ((FracChunkConstr v1 r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as FracHeapNull (FracHeapChunk Int))
                (ite (> r1 r2) (FracChunkConstr v1 (- r1 r2))
                  (as FracHeapTop (FracHeapChunk Int))))
              (as FracHeapTop (FracHeapChunk Int)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Int))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Int))) )))
(define-fun IntHeapChunkCompare ((x1 (FracHeapChunk Int))
            (x2 (FracHeapChunk Int))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))
(declare-fun BoolFracHeapValid ((FracHeap Bool)) Bool)
(assert
        (forall
                ((heap (FracHeap Bool)) (l Loc)
                 (chunk (FracHeapChunk Bool)))
                (=> (and (BoolFracHeapValid heap) (= (select heap l) chunk))
                   (match chunk ((FracHeapNull true) ((FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) (FracHeapTop false) )))))
(define-fun BoolFracChunkAdd ((x1 (FracHeapChunk Bool))
            (x2 (FracHeapChunk Bool))) (FracHeapChunk Bool)
             (match x1 ((FracHeapNull x2) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2))
              (as FracHeapTop (FracHeapChunk Bool)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Bool))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Bool))) )))
(define-fun BoolFracChunkSubtract ((x1 (FracHeapChunk Bool))
            (x2 (FracHeapChunk Bool))) (FracHeapChunk Bool)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
             (match x1 ((FracHeapNull
            (as FracHeapTop (FracHeapChunk Bool))) ((FracChunkConstr v1
                                                        r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as FracHeapNull (FracHeapChunk Bool))
                (ite (> r1 r2) (FracChunkConstr v1 (- r1 r2))
                  (as FracHeapTop (FracHeapChunk Bool))))
              (as FracHeapTop (FracHeapChunk Bool)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Bool))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Bool))) )))
(define-fun BoolHeapChunkCompare ((x1 (FracHeapChunk Bool))
            (x2 (FracHeapChunk Bool))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))
(declare-fun LocFracHeapValid ((FracHeap Loc)) Bool)
(assert
        (forall
                ((heap (FracHeap Loc)) (l Loc)
                 (chunk (FracHeapChunk Loc)))
                (=> (and (LocFracHeapValid heap) (= (select heap l) chunk))
                   (match chunk ((FracHeapNull true) ((FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) (FracHeapTop false) )))))
(define-fun LocFracChunkAdd ((x1 (FracHeapChunk Loc))
            (x2 (FracHeapChunk Loc))) (FracHeapChunk Loc)
             (match x1 ((FracHeapNull x2) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2))
              (as FracHeapTop (FracHeapChunk Loc)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Loc))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Loc))) )))
(define-fun LocFracChunkSubtract ((x1 (FracHeapChunk Loc))
            (x2 (FracHeapChunk Loc))) (FracHeapChunk Loc)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
             (match x1 ((FracHeapNull
            (as FracHeapTop (FracHeapChunk Loc))) ((FracChunkConstr v1
                                                        r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as FracHeapNull (FracHeapChunk Loc))
                (ite (> r1 r2) (FracChunkConstr v1 (- r1 r2))
                  (as FracHeapTop (FracHeapChunk Loc))))
              (as FracHeapTop (FracHeapChunk Loc)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Loc))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Loc))) )))
(define-fun LocHeapChunkCompare ((x1 (FracHeapChunk Loc))
            (x2 (FracHeapChunk Loc))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))


(declare-sort $Set 1)
(declare-sort $Map 2)

; ---------------------------------
; module GiveUpTemplate[K: Keyspace
(declare-sort K 0)
(declare-const KS ($Set K))

(declare-fun $select (($Set K) K) Bool)
(declare-fun $select (($Set Int) Int) Bool)

; , Node: NodeImpl[K]]

(declare-datatype Op ((searchOp) (insertOp) (deleteOp)))

(declare-datatype opSpecPred ((opSpecPredConstr (opSpecPredArg1 Op) (opSpecPredArg2 K) (opSpecPredArg3 ($Set K)) (opSpecPredArg4 ($Set K)) (opSpecPredArg5 Bool))))

(declare-sort FlowInt 0)

(declare-sort Node 0)

(declare-fun $select (($Set Node) Node) Bool)
(declare-fun $select (($Map Node Bool) Node) Bool)
(declare-fun $select (($Map Node FlowInt) Node) FlowInt)
(declare-fun $select (($Map Node ($Set K)) Node) ($Set K))

(declare-fun NodeFracHeapValid ((FracHeap Node)) Bool)
(assert
        (forall
                ((heap (FracHeap Node)) (l Loc)
                 (chunk (FracHeapChunk Node)))
                (=> (and (NodeFracHeapValid heap) (= (select heap l) chunk))
                   (match chunk ((FracHeapNull true) ((FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) (FracHeapTop false) )))))
(define-fun NodeFracChunkAdd ((x1 (FracHeapChunk Node))
            (x2 (FracHeapChunk Node))) (FracHeapChunk Node)
             (match x1 ((FracHeapNull x2) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (FracChunkConstr v1 (+ r1 r2))
              (as FracHeapTop (FracHeapChunk Node)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Node))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Node))) )))
(define-fun NodeFracChunkSubtract ((x1 (FracHeapChunk Node))
            (x2 (FracHeapChunk Node))) (FracHeapChunk Node)
             (match x2 ((FracHeapNull x1) ((FracChunkConstr v2 r2)
             (match x1 ((FracHeapNull
            (as FracHeapTop (FracHeapChunk Node))) ((FracChunkConstr v1
                                                        r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as FracHeapNull (FracHeapChunk Node))
                (ite (> r1 r2) (FracChunkConstr v1 (- r1 r2))
                  (as FracHeapTop (FracHeapChunk Node))))
              (as FracHeapTop (FracHeapChunk Node)))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Node))) ))) (FracHeapTop
            (as FracHeapTop (FracHeapChunk Node))) )))
(define-fun NodeHeapChunkCompare ((x1 (FracHeapChunk Node))
            (x2 (FracHeapChunk Node))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))

(declare-fun dom (FlowInt) ($Set Node))

(declare-datatype nodeRPred ((nodeRPredConstr (nodeRPredArg1 Node) (nodeRPredArg2 Bool) (nodeRPredArg3 FlowInt) (nodeRPredArg4 ($Set K)))))

; pred inFP
(declare-datatype inFPPred ((inFPPredConstr (inFPPredArg1 Loc) (inFPPredArg2 Node))))

; pred nodePred
(declare-datatype nodePredPred ((nodePredPredConstr (nodePredPredArg1 Loc) (nodePredPredArg2 Node) (nodePredPredArg3 FlowInt) (nodePredPredArg4 ($Set K)))))

; pred cssR
(declare-datatype cssRPred ((cssRPredConstr (cssRPredArg1 Loc) (cssRPredArg2 ($Set K)))))

; pred globalinv
(declare-datatype globalinvPred ((globalinvPredConstr (globalinvPredArg1 Loc) (globalinvPredArg2 FlowInt))))

; pred globalRes
(declare-datatype globalResPred ((globalResPredConstr (globalResPredArg1 Loc) (globalResPredArg2 FlowInt) (globalResPredArg3 ($Set K)))))

; inv cssI
(declare-datatype cssIPred ((cssIPredConstr (cssIPredArg1 Loc))))

(define-fun $Set_K_FracChunkAdd ((x1 (FracHeapChunk ($Set K))) (x2 (FracHeapChunk ($Set K)))) (FracHeapChunk ($Set K)) 
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

(define-fun $Set_K_FracChunkSubtract ((x1 (FracHeapChunk ($Set K))) (x2 (FracHeapChunk ($Set K)))) (FracHeapChunk ($Set K)) 
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

(declare-fun $Set_K_HeapValid ((FracHeap ($Set K))) Bool)
(assert (
	forall (
		(heap (FracHeap ($Set K)))
		(l Loc)
		(chunk (FracHeapChunk ($Set K)))
	)

	(=> 
		(and
			($Set_K_HeapValid heap)
			(= (select heap l) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunkConstr i r) (and (<= 0 r) (>= 1 r)))
            (FracHeapTop false)
        ))
	)
))

(define-fun $Set_K_HeapChunkCompare ((x1 (FracHeapChunk ($Set K)))
            (x2 (FracHeapChunk ($Set K)))) Bool
             (match x1 ((FracHeapNull true) ((FracChunkConstr v1 r1)
             (match x2 ((FracHeapNull false) ((FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) (FracHeapTop false) ))) (FracHeapTop
            false) )))

; proc cssOp(r: Ref, ghost C: $Set[K], dop: Op, k: K)
(declare-const r@0 Loc)
(declare-const C@0 ($Set K))
(declare-const dop@0 Op)
(declare-const k@0 K)

(declare-const cssIPredHeap@0 (PredHeap cssIPred))
(assert (forall ((index cssIPred)) (= 0 (select cssIPredHeap@0 index))))

(declare-const cssRPredHeap@0 (PredHeap cssRPred))
(assert (forall ((index cssRPred)) (= 0 (select cssRPredHeap@0 index))))

(declare-const globalResPredHeap@0 (PredHeap globalResPred))
(assert (forall ((index globalResPred)) (= 0 (select globalResPredHeap@0 index))))

(declare-const inFPPredHeap@0 (PredHeap inFPPred))
(assert (forall ((index inFPPred)) (= 0 (select inFPPredHeap@0 index))))

(declare-const nodeRPredHeap@0 (PredHeap nodeRPred))
(assert (forall ((index nodeRPred)) (= 0 (select nodeRPredHeap@0 index))))

(declare-const nodePredPredHeap@0 (PredHeap nodePredPred))
(assert (forall ((index nodePredPred)) (= 0 (select nodePredPredHeap@0 index))))

(declare-const nodeOwnHeap@0 (FracHeap Node))
(assert (NodeFracHeapValid nodeOwnHeap@0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk Node)) (select nodeOwnHeap@0 index))))

(declare-const rpOwnHeap@0 (FracHeap ($Set K)))
(assert ($Set_K_HeapValid rpOwnHeap@0))
(assert (forall ((index Loc)) (= (as FracHeapNull (FracHeapChunk ($Set K))) (select rpOwnHeap@0 index))))

; requires k in KS
(assert ($select KS k@0))

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

; openInv cssI(r)
; unfold cssI(r)

(declare-const cssIPredHeap@2 (PredHeap cssIPred))
(assert (= (- (select cssIPredHeap@1 (cssIPredConstr r@0)) 1) (select cssIPredHeap@2 (cssIPredConstr r@0))))
(assert (forall ((index cssIPred)) 
    (or
        (= index (cssIPredConstr r@0))
        (= (select cssIPredHeap@1 index) (select cssIPredHeap@2 index))
    )
))

(declare-const m_lk@0 ($Map Node Bool))
(declare-const m_In@0 ($Map Node FlowInt))
(declare-const m_Cn@0 ($Map Node ($Set K)))
(declare-const I@0 FlowInt)
(declare-const C@1 ($Set K))
(declare-const n@0 Node)

(declare-const rpOwnHeap@1 (FracHeap ($Set K)))
(assert ($Set_K_HeapValid rpOwnHeap@1))

(declare-const nodeOwnHeap@1 (FracHeap Node))
(declare-const inFPPredHeap@1 (PredHeap inFPPred))

(declare-const globalResPredHeap@1 (PredHeap globalResPred))

(declare-const nodeRPredHeap@1 (PredHeap nodeRPred))

(declare-const nodePredPredHeap@1 (PredHeap nodePredPred))

(assert (= (select rpOwnHeap@1 r@0) ($Set_K_FracChunkAdd (select rpOwnHeap@0 r@0) (FracChunkConstr C@1 (/ 1 2)))))
(assert (forall ((l Loc)) 
    (or 
        (= l r@0) 
        (= (select rpOwnHeap@1 l) (select rpOwnHeap@0 l))
    ) 
))

(assert (= (select nodeOwnHeap@1 r@0) (NodeFracChunkAdd (select nodeOwnHeap@0 r@0) (FracChunkConstr n@0 (/ 1 2)))))
(assert (forall ((l Loc)) 
    (or 
        (= l r@0) 
        (= (select nodeOwnHeap@1 l) (select nodeOwnHeap@0 l))
    ) 
))

(assert (= (select inFPPredHeap@1 (inFPPredConstr r@0 n@0)) (+ 1 (select inFPPredHeap@0 (inFPPredConstr r@0 n@0)))))
(assert (forall ((l Loc) (n1 Node))  
    (or
        (and (= l r@0) (= n1 n@0))
        (= (select inFPPredHeap@1 (inFPPredConstr l n1)) (select inFPPredHeap@0 (inFPPredConstr l n1)))
    )
))

(assert (= (select globalResPredHeap@1 (globalResPredConstr r@0 I@0 C@1)) (+ 1 (select globalResPredHeap@0 (globalResPredConstr r@0 I@0 C@1)))))
(assert (forall ((l Loc) (I1 FlowInt) (C1 ($Set K)))  
    (or
        (and (= l r@0) (= I1 I@0) (= C1 C@1))
        (= (select globalResPredHeap@1 (globalResPredConstr l I1 C1)) (select globalResPredHeap@0 (globalResPredConstr l I1 C1)))
    )
))

(assert (forall ((n Node))
    (=> ($select (dom I@0) n)
        (= (select nodeRPredHeap@1 (nodeRPredConstr n (select m_lk@0 n) (select m_In@0 n) (select m_Cn@0 n))) (+ 1 (select nodeRPredHeap@0 (nodeRPredConstr n (select m_lk@0 n) (select m_In@0 n) (select m_Cn@0 n)))))
    )
))

(assert (forall ((n1 Node) (lk1 Bool) (In1 FlowInt) (Cn1 ($Set K)))
    (or
        (exists ((n Node)) (and (= n n1) (= lk1 ($select m_lk@0 n)) (= In1 ($select m_In@0 n)) (= Cn1 ($select m_Cn@0 n)) ($select (dom I@0) n)))

        (= (select nodeRPredHeap@1 (nodeRPredConstr n1 lk1 In1 Cn1)) (select nodeRPredHeap@0 (nodeRPredConstr n1 lk1 In1 Cn1)))
    )
))

(assert (forall ((n Node))
    (=> (and ($select (dom I@0) n) ($select m_lk@0 n)) 
        (= (select nodePredPredHeap@1 (nodePredPredConstr r@0 n ($select m_In@0 n) ($select m_Cn@0 n))) (+ 1 (select nodePredPredHeap@0 (nodePredPredConstr r@0 n ($select m_In@0 n) ($select m_Cn@0 n)))))
    )
))

(assert (forall ((l1 Loc) (n1 Node) (In1 FlowInt) (Cn1 ($Set K)))
    (or
        (exists ((n Node)) (and (= l1 r@0) (= n1 n) (= In1 (select m_In@0 n)) (= Cn1 ($select m_Cn@0 n)) (and ($select (dom I@0) n) ($select m_lk@0 n))))

        (= (select nodePredPredHeap@1 (nodePredPredConstr l1 n1 In1 Cn1)) (select nodePredPredHeap@0 (nodePredPredConstr l1 n1 In1 Cn1)))
    )
))


; var v: Node = r.node
(declare-const v@0 Node)

; Check-permission
(push)
    (assert (not (exists ((n1 Node) (r1 Real)) 
        (and 
            (= (select nodeOwnHeap@1 r@0) (FracChunkConstr n1 r1))
            (> r1 0)
        )
    )))
    (check-sat)
(pop)

(assert (= v@0 (FracVal (select nodeOwnHeap@1 r@0))))

; inFP_persistent(r, v)


; check permission first 
(push)
    (assert (not (< 0 (select inFPPredHeap@1 (inFPPredConstr r@0 v@0)))))
    (check-sat)
(pop)

; exhale inFP(r,n)
(declare-const inFPPredHeap@2 (PredHeap inFPPred))
(assert (= (select inFPPredHeap@2 (inFPPredConstr r@0 v@0)) (- (select inFPPredHeap@1 (inFPPredConstr r@0 v@0)) 1)))
(assert (forall ((l Loc) (n Node)) 
    (or
        (and (= l r@0) (= n v@0))
        (= (select inFPPredHeap@2 (inFPPredConstr l n)) (select inFPPredHeap@1 (inFPPredConstr l n)))
    )
))

; inhale inFP(r,n) && inFP(r,n)
(declare-const inFPPredHeap@3 (PredHeap inFPPred))
(declare-const inFPPredHeap@4 (PredHeap inFPPred))

(assert (= (select inFPPredHeap@3 (inFPPredConstr r@0 v@0)) (+ (select inFPPredHeap@2 (inFPPredConstr r@0 v@0)) 1)))
(assert (forall ((l Loc) (n Node)) 
    (or
        (and (= l r@0) (= n v@0))
        (= (select inFPPredHeap@3 (inFPPredConstr l n)) (select inFPPredHeap@2 (inFPPredConstr l n)))
    )
))

(assert (= (select inFPPredHeap@4 (inFPPredConstr r@0 v@0)) (+ (select inFPPredHeap@3 (inFPPredConstr r@0 v@0)) 1)))
(assert (forall ((l Loc) (n Node)) 
    (or
        (and (= l r@0) (= n v@0))
        (= (select inFPPredHeap@3 (inFPPredConstr l n)) (select inFPPredHeap@2 (inFPPredConstr l n)))
    )
))

; fold cssI(r)

; check permission
(push)
    (assert (not (
        exists (
            (m_lk@1 ($Map Node Bool)) (m_In@1 ($Map Node FlowInt)) (m_Cn@1 ($Map Node ($Set K))) (I@1 FlowInt) 
            (C@2 ($Set K)) 
            (n@1 Node)
        )

            (and
                ($Set_K_HeapChunkCompare (FracChunkConstr C@2 (/ 1 2)) (select rpOwnHeap@1 r@0))
                (NodeHeapChunkCompare (FracChunkConstr n@1 (/ 1 2)) (select nodeOwnHeap@1 r@0))
                (< 0 (select inFPPredHeap@4 (inFPPredConstr r@0 n@1)))
                (< 0 (select globalResPredHeap@1 (globalResPredConstr r@0 I@1 C@2)))
                ; (forall ((n1 Node)) 
                ;     (=> ($select (dom I@1) n1)
                ;         (< 0 (select nodeRPredHeap@1 (nodeRPredConstr n1 (select m_lk@1 n1) (select m_In@1 n1) (select m_Cn@1 n1))))
                ;     )
                ; )
                ; (forall ((n1 Node))
                ;     (=> (and ($select (dom I@1) n1) ($select m_lk@1 n1))
                ;         (< 0 (select nodePredPredHeap@1 (nodePredPredConstr r@0 n1 ($select m_In@1 n1) ($select m_Cn@1 n1))))
                    
                ;     )
                ; )
            )
    )))
    (check-sat)
    ; (get-model)
(pop)

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
                ; (forall ((n1 Node))
                ;     (=> (and ($select (dom I@1) n1) ($select m_lk@1 n1))
                ;         (< 0 (select nodePredPredHeap@1 (nodePredPredConstr r@0 n1 ($select m_In@1 n1) ($select m_Cn@1 n1))))
                    
                ;     )
                ; )
            )
    )))
    (check-sat)
    ; (get-model)
(pop)
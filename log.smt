(declare-sort $Loc 0)
(declare-datatype
                   $FracHeapChunk (par (T) ( ($FracHeapNull)
                   ($FracChunkConstr ($FracVal T) ($FracOwn Real))
                   ($FracHeapTop))))
(define-sort $FracHeap (T) (Array $Loc ($FracHeapChunk T)))
(define-sort $PredHeap (T) (Array T Int))
(declare-fun $IntFracHeapValid (($FracHeap Int)) Bool)
(assert
        (forall ((heap ($FracHeap Int)) (l $Loc))
                (=> ($IntFracHeapValid heap)
                   (match (select heap l) (($FracHeapNull
                  true) (($FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) ($FracHeapTop false) )))))
(define-fun $IntFracChunkAdd ((x1 ($FracHeapChunk Int))
            (x2 ($FracHeapChunk Int))) ($FracHeapChunk Int)
             (match x1 (($FracHeapNull x2) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) ($FracChunkConstr v1 (+ r1 r2))
              (as $FracHeapTop ($FracHeapChunk Int)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Int))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Int))) )))
(define-fun $IntFracChunkSubtract ((x1 ($FracHeapChunk Int))
            (x2 ($FracHeapChunk Int))) ($FracHeapChunk Int)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
             (match x1 (($FracHeapNull
            (as $FracHeapTop ($FracHeapChunk Int))) (($FracChunkConstr v1 r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as $FracHeapNull ($FracHeapChunk Int))
                (ite (> r1 r2) ($FracChunkConstr v1 (- r1 r2))
                  (as $FracHeapTop ($FracHeapChunk Int))))
              (as $FracHeapTop ($FracHeapChunk Int)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Int))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Int))) )))
(define-fun $IntHeapChunkCompare ((x1 ($FracHeapChunk Int))
            (x2 ($FracHeapChunk Int))) Bool
             (match x1 (($FracHeapNull true) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull false) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) ($FracHeapTop false) ))) ($FracHeapTop
            false) )))
(declare-fun $BoolFracHeapValid (($FracHeap Bool)) Bool)
(assert
        (forall ((heap ($FracHeap Bool)) (l $Loc))
                (=> ($BoolFracHeapValid heap)
                   (match (select heap l) (($FracHeapNull
                  true) (($FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) ($FracHeapTop false) )))))
(define-fun $BoolFracChunkAdd ((x1 ($FracHeapChunk Bool))
            (x2 ($FracHeapChunk Bool))) ($FracHeapChunk Bool)
             (match x1 (($FracHeapNull x2) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) ($FracChunkConstr v1 (+ r1 r2))
              (as $FracHeapTop ($FracHeapChunk Bool)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Bool))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Bool))) )))
(define-fun $BoolFracChunkSubtract ((x1 ($FracHeapChunk Bool))
            (x2 ($FracHeapChunk Bool))) ($FracHeapChunk Bool)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
             (match x1 (($FracHeapNull
            (as $FracHeapTop ($FracHeapChunk Bool))) (($FracChunkConstr v1
                                                        r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as $FracHeapNull ($FracHeapChunk Bool))
                (ite (> r1 r2) ($FracChunkConstr v1 (- r1 r2))
                  (as $FracHeapTop ($FracHeapChunk Bool))))
              (as $FracHeapTop ($FracHeapChunk Bool)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Bool))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk Bool))) )))
(define-fun $BoolHeapChunkCompare ((x1 ($FracHeapChunk Bool))
            (x2 ($FracHeapChunk Bool))) Bool
             (match x1 (($FracHeapNull true) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull false) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) ($FracHeapTop false) ))) ($FracHeapTop
            false) )))
(declare-fun $LocFracHeapValid (($FracHeap $Loc)) Bool)
(assert
        (forall ((heap ($FracHeap $Loc)) (l $Loc))
                (=> ($LocFracHeapValid heap)
                   (match (select heap l) (($FracHeapNull
                  true) (($FracChunkConstr i r)
                  (and (<= 0 r) (>= 1 r))) ($FracHeapTop false) )))))
(define-fun $LocFracChunkAdd ((x1 ($FracHeapChunk $Loc))
            (x2 ($FracHeapChunk $Loc))) ($FracHeapChunk $Loc)
             (match x1 (($FracHeapNull x2) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) ($FracChunkConstr v1 (+ r1 r2))
              (as $FracHeapTop ($FracHeapChunk $Loc)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk $Loc))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk $Loc))) )))
(define-fun $LocFracChunkSubtract ((x1 ($FracHeapChunk $Loc))
            (x2 ($FracHeapChunk $Loc))) ($FracHeapChunk $Loc)
             (match x2 (($FracHeapNull x1) (($FracChunkConstr v2 r2)
             (match x1 (($FracHeapNull
            (as $FracHeapTop ($FracHeapChunk $Loc))) (($FracChunkConstr v1
                                                        r1)
            (ite (= v1 v2)
              (ite (= r1 r2) (as $FracHeapNull ($FracHeapChunk $Loc))
                (ite (> r1 r2) ($FracChunkConstr v1 (- r1 r2))
                  (as $FracHeapTop ($FracHeapChunk $Loc))))
              (as $FracHeapTop ($FracHeapChunk $Loc)))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk $Loc))) ))) ($FracHeapTop
            (as $FracHeapTop ($FracHeapChunk $Loc))) )))
(define-fun $LocHeapChunkCompare ((x1 ($FracHeapChunk $Loc))
            (x2 ($FracHeapChunk $Loc))) Bool
             (match x1 (($FracHeapNull true) (($FracChunkConstr v1 r1)
             (match x2 (($FracHeapNull false) (($FracChunkConstr v2 r2)
            (ite (= v1 v2) (<= r1 r2) false)) ($FracHeapTop false) ))) ($FracHeapTop
            false) )))

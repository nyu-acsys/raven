(set-option :timeout 2000)
(declare-sort $Loc 0)
(declare-datatype
                   $FracHeapChunk (par (T) ( ($FracHeapNull)
                   ($FracChunkConstr ($FracVal T) ($FracOwn Real))
                   ($FracHeapTop))))
(define-sort $OwnHeap (T) (Array $Loc T))
(define-sort $PredHeap (T) (Array T Int))
(declare-fun $IntFracHeapValid (($OwnHeap ($FracHeapChunk Int))) Bool)
(assert
        (forall ((heap ($OwnHeap ($FracHeapChunk Int))) (l $Loc))
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
(declare-fun $BoolFracHeapValid (($OwnHeap ($FracHeapChunk Bool))) Bool)
(assert
        (forall ((heap ($OwnHeap ($FracHeapChunk Bool))) (l $Loc))
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
(declare-fun $LocFracHeapValid (($OwnHeap ($FracHeapChunk $Loc))) Bool)
(assert
        (forall ((heap ($OwnHeap ($FracHeapChunk $Loc))) (l $Loc))
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
; End of Preamble
; 
; 
; 
; 
; Entering module Lib.
; 
; 
; Entering module Lib.Type.
(declare-sort Lib.Type.T 0)
; 
; 
; Entering module Lib.ResourceAlgebra.
(declare-sort Lib.ResourceAlgebra.T 0)
(declare-const Lib.ResourceAlgebra.id Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.comp (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.frame (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.valid (Lib.ResourceAlgebra.T) Bool)
(declare-fun Lib.ResourceAlgebra.fpuAllowed (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Bool)
; 
; 
; Entering module Lib.CancellativeResourceAlgebra.
(declare-sort Lib.CancellativeResourceAlgebra.T 0)
(declare-const Lib.CancellativeResourceAlgebra.id
             Lib.CancellativeResourceAlgebra.T)
(declare-fun Lib.CancellativeResourceAlgebra.comp
             (Lib.CancellativeResourceAlgebra.T
             Lib.CancellativeResourceAlgebra.T)
             Lib.CancellativeResourceAlgebra.T)
(declare-fun Lib.CancellativeResourceAlgebra.frame
             (Lib.CancellativeResourceAlgebra.T
             Lib.CancellativeResourceAlgebra.T)
             Lib.CancellativeResourceAlgebra.T)
(declare-fun Lib.CancellativeResourceAlgebra.valid
             (Lib.CancellativeResourceAlgebra.T) Bool)
(declare-fun Lib.CancellativeResourceAlgebra.fpuAllowed
             (Lib.CancellativeResourceAlgebra.T
             Lib.CancellativeResourceAlgebra.T) Bool)
; 
; 
; Entering module Lib.LatticeResourceAlgebra.
(declare-sort Lib.LatticeResourceAlgebra.T 0)
(declare-const Lib.LatticeResourceAlgebra.id Lib.LatticeResourceAlgebra.T)
(declare-fun Lib.LatticeResourceAlgebra.comp (Lib.LatticeResourceAlgebra.T
             Lib.LatticeResourceAlgebra.T) Lib.LatticeResourceAlgebra.T)
(declare-fun Lib.LatticeResourceAlgebra.frame (Lib.LatticeResourceAlgebra.T
             Lib.LatticeResourceAlgebra.T) Lib.LatticeResourceAlgebra.T)
(declare-fun Lib.LatticeResourceAlgebra.valid (Lib.LatticeResourceAlgebra.T)
             Bool)
(declare-fun Lib.LatticeResourceAlgebra.fpuAllowed
             (Lib.LatticeResourceAlgebra.T Lib.LatticeResourceAlgebra.T)
             Bool)
; 
; 
; Entering module Lib.Nat.
(declare-const Lib.Nat.id Int)
(assert (= Lib.Nat.id 0))
(define-fun Lib.Nat.valid ((n Int)) Bool (>= n 0))
(define-fun Lib.Nat.comp ((a^20 Int) (b^15 Int)) Int
            (ite (= a^20 Lib.Nat.id) b^15
              (ite (= b^15 Lib.Nat.id) a^20
                (ite (and (Lib.Nat.valid a^20) (Lib.Nat.valid b^15))
                  (+ a^20 b^15) (* -1 1)))))
(define-fun Lib.Nat.frame ((a^21 Int) (b^16 Int)) Int
            (ite (= b^16 Lib.Nat.id) a^21
              (ite (and (Lib.Nat.valid a^21) (Lib.Nat.valid b^16))
                (- a^21 b^16) (* -1 1))))
(define-fun Lib.Nat.fpuAllowed ((a^22 Int) (b^17 Int)) Bool
            (forall ((c Int))
                    (=>
                      (and (Lib.Nat.valid a^22)
                        (Lib.Nat.valid (Lib.Nat.comp a^22 c)))
                      (Lib.Nat.valid (Lib.Nat.comp b^17 c)))))
(push 1)
; Initializing vars for proc_def Lib.Nat.weak_frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$1 Int) (b$1 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$1 b$1))
                    (Lib.Nat.valid
                      (Lib.Nat.frame (Lib.Nat.comp a$1 b$1) b$1))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.idValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (Lib.Nat.valid Lib.Nat.id)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.frameValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$2 Int) (b$2 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.frame a$2 b$2))
                    (and (Lib.Nat.valid a$2) (Lib.Nat.valid b$2))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$3 Int)) (= (Lib.Nat.frame a$3 Lib.Nat.id) a$3))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$4 Int) (b$3 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$4 b$3))
                    (= (Lib.Nat.frame (Lib.Nat.comp a$4 b$3) b$3) a$4)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$5 Int) (b$4 Int) (c$1 Int))
                  (=>
                    (and
                      (and (Lib.Nat.fpuAllowed a$5 b$4) (Lib.Nat.valid a$5))
                      (Lib.Nat.valid (Lib.Nat.comp a$5 c$1)))
                    (Lib.Nat.valid (Lib.Nat.comp b$4 c$1))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.fpuReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$6 Int))
                  (=> (Lib.Nat.valid a$6) (Lib.Nat.fpuAllowed a$6 a$6)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$7 Int) (b$5 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$7 b$5))
                    (and (Lib.Nat.valid a$7) (Lib.Nat.valid b$5))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$8 Int)) (= (Lib.Nat.comp a$8 Lib.Nat.id) a$8))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$9 Int) (b$6 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.frame a$9 b$6))
                    (= (Lib.Nat.comp (Lib.Nat.frame a$9 b$6) b$6) a$9)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$10 Int) (b$7 Int))
                  (= (Lib.Nat.comp a$10 b$7) (Lib.Nat.comp b$7 a$10)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$11 Int) (b$8 Int) (c$2 Int))
                  (= (Lib.Nat.comp (Lib.Nat.comp a$11 b$8) c$2)
                    (Lib.Nat.comp a$11 (Lib.Nat.comp b$8 c$2))))))
(check-sat)
(pop 1)
(pop 1)
; 
; 
; Entering module Lib.Auth.
(declare-sort Lib.Auth.M.T 0)
(declare-const Lib.Auth.M.id Lib.Auth.M.T)
(declare-fun Lib.Auth.M.comp (Lib.Auth.M.T Lib.Auth.M.T) Lib.Auth.M.T)
(declare-fun Lib.Auth.M.frame (Lib.Auth.M.T Lib.Auth.M.T) Lib.Auth.M.T)
(declare-fun Lib.Auth.M.valid (Lib.Auth.M.T) Bool)
(declare-fun Lib.Auth.M.fpuAllowed (Lib.Auth.M.T Lib.Auth.M.T) Bool)
; Asserting axiom frameCompInv
(assert
        (forall ((a$12 Lib.Auth.M.T) (b$9 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$12 b$9))
                  (= (Lib.Auth.M.frame a$12 b$9) a$12))))
; Asserting axiom frameCompInv0
(assert
        (forall ((a$13 Lib.Auth.M.T) (b$10 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$13 b$10))
                  (= (Lib.Auth.M.frame (Lib.Auth.M.comp a$13 b$10) b$10)
                    (Lib.Auth.M.comp a$13 b$10)))))
; Asserting axiom frameCompInv2
(assert
        (forall ((a$14 Lib.Auth.M.T) (b$11 Lib.Auth.M.T))
                (=>
                  (and (= (Lib.Auth.M.comp a$14 b$11) a$14)
                    (Lib.Auth.M.valid a$14))
                  (= (Lib.Auth.M.frame a$14 b$11) a$14))))
; Asserting axiom frame_comp_inv
(assert
        (forall ((a$15 Lib.Auth.M.T) (b$12 Lib.Auth.M.T) (c$3 Lib.Auth.M.T))
                (= (Lib.Auth.M.frame a$15 (Lib.Auth.M.comp b$12 c$3))
                  (Lib.Auth.M.frame (Lib.Auth.M.frame a$15 b$12) c$3))))
; Asserting axiom weak_frameCompInv
(assert
        (forall ((a$16 Lib.Auth.M.T) (b$13 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$16 b$13))
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.M.comp a$16 b$13) b$13)))))
; Asserting axiom idValid
(assert (Lib.Auth.M.valid Lib.Auth.M.id))
; Asserting axiom frameValid
(assert
        (forall ((a$17 Lib.Auth.M.T) (b$14 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$17 b$14))
                  (and (Lib.Auth.M.valid a$17) (Lib.Auth.M.valid b$14)))))
; Asserting axiom frameId
(assert
        (forall ((a$18 Lib.Auth.M.T))
                (= (Lib.Auth.M.frame a$18 Lib.Auth.M.id) a$18)))
; Asserting axiom fpuValid
(assert
        (forall ((a$19 Lib.Auth.M.T) (b$15 Lib.Auth.M.T) (c$4 Lib.Auth.M.T))
                (=>
                  (and
                    (and (Lib.Auth.M.fpuAllowed a$19 b$15)
                      (Lib.Auth.M.valid a$19))
                    (Lib.Auth.M.valid (Lib.Auth.M.comp a$19 c$4)))
                  (Lib.Auth.M.valid (Lib.Auth.M.comp b$15 c$4)))))
; Asserting axiom fpuReflexive
(assert
        (forall ((a$20 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid a$20)
                  (Lib.Auth.M.fpuAllowed a$20 a$20))))
; Asserting axiom compValid
(assert
        (forall ((a$21 Lib.Auth.M.T) (b$16 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$21 b$16))
                  (and (Lib.Auth.M.valid a$21) (Lib.Auth.M.valid b$16)))))
; Asserting axiom compId
(assert
        (forall ((a$22 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$22 Lib.Auth.M.id) a$22)))
; Asserting axiom compFrameInv
(assert
        (forall ((a$23 Lib.Auth.M.T) (b$17 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$23 b$17))
                  (= (Lib.Auth.M.comp (Lib.Auth.M.frame a$23 b$17) b$17)
                    a$23))))
; Asserting axiom compCommute
(assert
        (forall ((a$24 Lib.Auth.M.T) (b$18 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$24 b$18) (Lib.Auth.M.comp b$18 a$24))))
; Asserting axiom compAssoc
(assert
        (forall ((a$25 Lib.Auth.M.T) (b$19 Lib.Auth.M.T) (c$5 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp (Lib.Auth.M.comp a$25 b$19) c$5)
                  (Lib.Auth.M.comp a$25 (Lib.Auth.M.comp b$19 c$5)))))
(declare-datatype
                   Lib.Auth.T ( (Lib.Auth.frag (Lib.Auth.f_proj1
                   Lib.Auth.M.T)) (Lib.Auth.auth_frag (Lib.Auth.af_proj1
                   Lib.Auth.M.T) (Lib.Auth.af_proj2 Lib.Auth.M.T))
                   (Lib.Auth.top)))
(declare-const Lib.Auth.id Lib.Auth.T)
(assert (= Lib.Auth.id (Lib.Auth.frag Lib.Auth.M.id)))
(define-fun Lib.Auth.valid ((n^1 Lib.Auth.T)) Bool
            (ite (= n^1 (Lib.Auth.frag (Lib.Auth.f_proj1 n^1)))
              (Lib.Auth.M.valid (Lib.Auth.f_proj1 n^1))
              (ite
                (= n^1
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 n^1)
                    (Lib.Auth.af_proj2 n^1)))
                (and
                  (and (Lib.Auth.M.valid (Lib.Auth.af_proj1 n^1))
                    (Lib.Auth.M.valid (Lib.Auth.af_proj2 n^1)))
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.af_proj1 n^1)
                      (Lib.Auth.af_proj2 n^1))))
                false)))
(define-fun Lib.Auth.comp ((a^39 Lib.Auth.T) (b^30 Lib.Auth.T)) Lib.Auth.T
            (ite
              (and (= a^39 (Lib.Auth.frag (Lib.Auth.f_proj1 a^39)))
                (= b^30 (Lib.Auth.frag (Lib.Auth.f_proj1 b^30))))
              (Lib.Auth.frag
                (Lib.Auth.M.comp (Lib.Auth.f_proj1 a^39)
                  (Lib.Auth.f_proj1 b^30)))
              (ite
                (and (= a^39 (Lib.Auth.frag (Lib.Auth.f_proj1 a^39)))
                  (= b^30
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^30)
                      (Lib.Auth.af_proj2 b^30))))
                (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^30)
                  (Lib.Auth.M.comp (Lib.Auth.f_proj1 a^39)
                    (Lib.Auth.af_proj2 b^30)))
                (ite
                  (and
                    (= a^39
                      (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^39)
                        (Lib.Auth.af_proj2 a^39)))
                    (= b^30 (Lib.Auth.frag (Lib.Auth.f_proj1 b^30))))
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^39)
                    (Lib.Auth.M.comp (Lib.Auth.f_proj1 b^30)
                      (Lib.Auth.af_proj2 a^39)))
                  Lib.Auth.top))))
(define-fun Lib.Auth.frame ((a^40 Lib.Auth.T) (b^31 Lib.Auth.T)) Lib.Auth.T
            (ite (= b^31 Lib.Auth.id) a^40
              (ite
                (and (= a^40 (Lib.Auth.frag (Lib.Auth.f_proj1 a^40)))
                  (= b^31 (Lib.Auth.frag (Lib.Auth.f_proj1 b^31))))
                (Lib.Auth.frag
                  (Lib.Auth.M.frame (Lib.Auth.f_proj1 a^40)
                    (Lib.Auth.f_proj1 b^31)))
                (ite
                  (and (= a^40 (Lib.Auth.frag (Lib.Auth.f_proj1 a^40)))
                    (= b^31
                      (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^31)
                        (Lib.Auth.af_proj2 b^31))))
                  Lib.Auth.top
                  (ite
                    (and
                      (and
                        (= a^40
                          (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^40)
                            (Lib.Auth.af_proj2 a^40)))
                        (Lib.Auth.valid a^40))
                      (= b^31 (Lib.Auth.frag (Lib.Auth.f_proj1 b^31))))
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^40)
                      (Lib.Auth.M.frame (Lib.Auth.af_proj2 a^40)
                        (Lib.Auth.f_proj1 b^31)))
                    (ite
                      (and
                        (and
                          (= a^40
                            (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^40)
                              (Lib.Auth.af_proj2 a^40)))
                          (Lib.Auth.valid a^40))
                        (= b^31
                          (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^31)
                            (Lib.Auth.af_proj2 b^31))))
                      (ite
                        (= (Lib.Auth.af_proj1 a^40) (Lib.Auth.af_proj1 b^31))
                        (Lib.Auth.frag
                          (Lib.Auth.M.frame (Lib.Auth.af_proj2 a^40)
                            (Lib.Auth.af_proj2 b^31)))
                        Lib.Auth.top)
                      Lib.Auth.top))))))
(define-fun Lib.Auth.fpuAllowed ((a^41 Lib.Auth.T) (b^32 Lib.Auth.T)) Bool
            (ite (= a^41 b^32) true
              (ite
                (and
                  (= a^41
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^41)
                      (Lib.Auth.af_proj2 a^41)))
                  (= b^32
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^32)
                      (Lib.Auth.af_proj2 b^32))))
                (and
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.af_proj1 b^32)
                      (Lib.Auth.af_proj1 a^41)))
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame
                      (Lib.Auth.M.frame (Lib.Auth.af_proj1 b^32)
                        (Lib.Auth.af_proj2 b^32))
                      (Lib.Auth.M.frame (Lib.Auth.af_proj1 a^41)
                        (Lib.Auth.af_proj2 a^41)))))
                false)))
(push 1)
; Initializing vars for proc_def Lib.Auth.weak_frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$26 Lib.Auth.T) (b$20 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$26 b$20))
                    (Lib.Auth.valid
                      (Lib.Auth.frame (Lib.Auth.comp a$26 b$20) b$20))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.idValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (Lib.Auth.valid Lib.Auth.id)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.frameValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$27 Lib.Auth.T) (b$21 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.frame a$27 b$21))
                    (and (Lib.Auth.valid a$27) (Lib.Auth.valid b$21))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$28 Lib.Auth.T))
                  (= (Lib.Auth.frame a$28 Lib.Auth.id) a$28))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions

(declare-const a$29 Lib.Auth.T)
(declare-const tmp1 Lib.Auth.M.T)
(declare-const tmp2 Lib.Auth.M.T)
; (assert (= a$29 (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a$29) (Lib.Auth.af_proj2 a$29))))
; (assert (= a$29 (Lib.Auth.auth_frag tmp1 tmp2)))

; (assert (= a$29 (Lib.Auth.frag tmp1)))
; (assert (= a$29 (Lib.Auth.frag (Lib.Auth.f_proj1 a$29))))

; (assert (= a$29 Lib.Auth.top))

(declare-const b$22 Lib.Auth.T)
(declare-const tmp3 Lib.Auth.M.T)
(declare-const tmp4 Lib.Auth.M.T)
(assert (= b$22 (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b$22) (Lib.Auth.af_proj2 b$22))))
; (assert (= b$22 (Lib.Auth.auth_frag tmp3 tmp4)))

; (assert (= b$22 (Lib.Auth.frag (Lib.Auth.f_proj1 b$22))))
; (assert (= b$22 (Lib.Auth.frag tmp3)))

; (assert (= b$22 Lib.Auth.top))

(declare-const c$6 Lib.Auth.T)

(push 1)
(assert
        (not
                  (=>
                    (and
                      (and (Lib.Auth.fpuAllowed a$29 b$22)
                        (Lib.Auth.valid a$29))
                      (Lib.Auth.valid (Lib.Auth.comp a$29 c$6)))
                    (Lib.Auth.valid (Lib.Auth.comp b$22 c$6)))))
(check-sat)
; (get-model)
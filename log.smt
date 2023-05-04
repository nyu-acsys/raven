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
; Initializing vars for proc_def Lib.Nat.frameReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$3 Int))
                  (=> (Lib.Nat.valid a$3)
                    (= (Lib.Nat.frame a$3 a$3) Lib.Nat.id)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$4 Int)) (= (Lib.Nat.frame a$4 Lib.Nat.id) a$4))))
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
          (forall ((a$5 Int) (b$3 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$5 b$3))
                    (= (Lib.Nat.frame (Lib.Nat.comp a$5 b$3) b$3) a$5)))))
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
          (forall ((a$6 Int) (b$4 Int) (c$1 Int))
                  (=>
                    (and
                      (and (Lib.Nat.fpuAllowed a$6 b$4) (Lib.Nat.valid a$6))
                      (Lib.Nat.valid (Lib.Nat.comp a$6 c$1)))
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
          (forall ((a$7 Int))
                  (=> (Lib.Nat.valid a$7) (Lib.Nat.fpuAllowed a$7 a$7)))))
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
          (forall ((a$8 Int) (b$5 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$8 b$5))
                    (and (Lib.Nat.valid a$8) (Lib.Nat.valid b$5))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$9 Int)) (= (Lib.Nat.comp a$9 Lib.Nat.id) a$9))))
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
          (forall ((a$10 Int) (b$6 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.frame a$10 b$6))
                    (= (Lib.Nat.comp (Lib.Nat.frame a$10 b$6) b$6) a$10)))))
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
          (forall ((a$11 Int) (b$7 Int))
                  (= (Lib.Nat.comp a$11 b$7) (Lib.Nat.comp b$7 a$11)))))
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
          (forall ((a$12 Int) (b$8 Int) (c$2 Int))
                  (= (Lib.Nat.comp (Lib.Nat.comp a$12 b$8) c$2)
                    (Lib.Nat.comp a$12 (Lib.Nat.comp b$8 c$2))))))
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
        (forall ((a$13 Lib.Auth.M.T) (b$9 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$13 b$9))
                  (= (Lib.Auth.M.frame (Lib.Auth.M.comp a$13 b$9) b$9) a$13))))
; Asserting axiom frameReflexive
(assert
        (forall ((a$14 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid a$14)
                  (= (Lib.Auth.M.frame a$14 a$14) Lib.Auth.M.id))))
; Asserting axiom weak_frameCompInv
(assert
        (forall ((a$15 Lib.Auth.M.T) (b$10 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$15 b$10))
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.M.comp a$15 b$10) b$10)))))
; Asserting axiom idValid
(assert (Lib.Auth.M.valid Lib.Auth.M.id))
; Asserting axiom frameValid
(assert
        (forall ((a$16 Lib.Auth.M.T) (b$11 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$16 b$11))
                  (and (Lib.Auth.M.valid a$16) (Lib.Auth.M.valid b$11)))))
; Asserting axiom frameId
(assert
        (forall ((a$17 Lib.Auth.M.T))
                (= (Lib.Auth.M.frame a$17 Lib.Auth.M.id) a$17)))
; Asserting axiom fpuValid
(assert
        (forall ((a$18 Lib.Auth.M.T) (b$12 Lib.Auth.M.T) (c$3 Lib.Auth.M.T))
                (=>
                  (and
                    (and (Lib.Auth.M.fpuAllowed a$18 b$12)
                      (Lib.Auth.M.valid a$18))
                    (Lib.Auth.M.valid (Lib.Auth.M.comp a$18 c$3)))
                  (Lib.Auth.M.valid (Lib.Auth.M.comp b$12 c$3)))))
; Asserting axiom fpuReflexive
(assert
        (forall ((a$19 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid a$19)
                  (Lib.Auth.M.fpuAllowed a$19 a$19))))
; Asserting axiom compValid
(assert
        (forall ((a$20 Lib.Auth.M.T) (b$13 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$20 b$13))
                  (and (Lib.Auth.M.valid a$20) (Lib.Auth.M.valid b$13)))))
; Asserting axiom compId
(assert
        (forall ((a$21 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$21 Lib.Auth.M.id) a$21)))
; Asserting axiom compFrameInv
(assert
        (forall ((a$22 Lib.Auth.M.T) (b$14 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$22 b$14))
                  (= (Lib.Auth.M.comp (Lib.Auth.M.frame a$22 b$14) b$14)
                    a$22))))
; Asserting axiom compCommute
(assert
        (forall ((a$23 Lib.Auth.M.T) (b$15 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$23 b$15) (Lib.Auth.M.comp b$15 a$23))))
; Asserting axiom compAssoc
(assert
        (forall ((a$24 Lib.Auth.M.T) (b$16 Lib.Auth.M.T) (c$4 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp (Lib.Auth.M.comp a$24 b$16) c$4)
                  (Lib.Auth.M.comp a$24 (Lib.Auth.M.comp b$16 c$4)))))
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
          (forall ((a$25 Lib.Auth.T) (b$17 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$25 b$17))
                    (Lib.Auth.valid
                      (Lib.Auth.frame (Lib.Auth.comp a$25 b$17) b$17))))))
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
          (forall ((a$26 Lib.Auth.T) (b$18 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.frame a$26 b$18))
                    (and (Lib.Auth.valid a$26) (Lib.Auth.valid b$18))))))
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
          (forall ((a$27 Lib.Auth.T))
                  (= (Lib.Auth.frame a$27 Lib.Auth.id) a$27))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$28 Lib.Auth.T) (b$19 Lib.Auth.T) (c$5 Lib.Auth.T))
                  (=>
                    (and
                      (and (Lib.Auth.fpuAllowed a$28 b$19)
                        (Lib.Auth.valid a$28))
                      (Lib.Auth.valid (Lib.Auth.comp a$28 c$5)))
                    (Lib.Auth.valid (Lib.Auth.comp b$19 c$5))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.fpuReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$29 Lib.Auth.T))
                  (=> (Lib.Auth.valid a$29) (Lib.Auth.fpuAllowed a$29 a$29)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$30 Lib.Auth.T) (b$20 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$30 b$20))
                    (and (Lib.Auth.valid a$30) (Lib.Auth.valid b$20))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$31 Lib.Auth.T))
                  (= (Lib.Auth.comp a$31 Lib.Auth.id) a$31))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$32 Lib.Auth.T) (b$21 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.frame a$32 b$21))
                    (= (Lib.Auth.comp (Lib.Auth.frame a$32 b$21) b$21) a$32)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$33 Lib.Auth.T) (b$22 Lib.Auth.T))
                  (= (Lib.Auth.comp a$33 b$22) (Lib.Auth.comp b$22 a$33)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$34 Lib.Auth.T) (b$23 Lib.Auth.T) (c$6 Lib.Auth.T))
                  (= (Lib.Auth.comp (Lib.Auth.comp a$34 b$23) c$6)
                    (Lib.Auth.comp a$34 (Lib.Auth.comp b$23 c$6))))))
(check-sat)
(pop 1)
(pop 1)
; 
; 
; Entering module Lib.Frac.
(declare-sort Lib.Frac.X.T 0)
(declare-datatype
                   Lib.Frac.T ( (Lib.Frac.frac_null) (Lib.Frac.frac_chunk
                   (Lib.Frac.frac_proj1 Lib.Frac.X.T) (Lib.Frac.frac_proj2
                   Real)) (Lib.Frac.frac_top)))
(declare-const Lib.Frac.id Lib.Frac.T)
(assert (= Lib.Frac.id Lib.Frac.frac_null))
(define-fun Lib.Frac.valid ((n^2 Lib.Frac.T)) Bool
            (ite
              (= n^2
                (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 n^2)
                  (Lib.Frac.frac_proj2 n^2)))
              (and (> (Lib.Frac.frac_proj2 n^2) 0)
                (<= (Lib.Frac.frac_proj2 n^2) 1))
              (ite (= n^2 Lib.Frac.frac_null) true false)))
(define-fun Lib.Frac.comp ((a^46 Lib.Frac.T) (b^36 Lib.Frac.T)) Lib.Frac.T
            (ite (= a^46 Lib.Frac.frac_null) b^36
              (ite (= b^36 Lib.Frac.frac_null) a^46
                (ite (and (Lib.Frac.valid a^46) (Lib.Frac.valid b^36))
                  (ite
                    (and
                      (and
                        (= (Lib.Frac.frac_proj1 a^46)
                          (Lib.Frac.frac_proj1 b^36))
                        (>
                          (+ (Lib.Frac.frac_proj2 a^46)
                            (Lib.Frac.frac_proj2 b^36))
                          0))
                      (<=
                        (+ (Lib.Frac.frac_proj2 a^46)
                          (Lib.Frac.frac_proj2 b^36))
                        1))
                    (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^46)
                      (+ (Lib.Frac.frac_proj2 a^46)
                        (Lib.Frac.frac_proj2 b^36)))
                    Lib.Frac.frac_top)
                  Lib.Frac.frac_top))))
(define-fun Lib.Frac.frame ((a^47 Lib.Frac.T) (b^37 Lib.Frac.T)) Lib.Frac.T
            (ite (= b^37 Lib.Frac.frac_null) a^47
              (ite
                (and
                  (and
                    (and
                      (= a^47
                        (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^47)
                          (Lib.Frac.frac_proj2 a^47)))
                      (= b^37
                        (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 b^37)
                          (Lib.Frac.frac_proj2 b^37))))
                    (Lib.Frac.valid a^47))
                  (Lib.Frac.valid b^37))
                (ite
                  (= (Lib.Frac.frac_proj1 a^47) (Lib.Frac.frac_proj1 b^37))
                  (ite
                    (= (Lib.Frac.frac_proj2 a^47) (Lib.Frac.frac_proj2 b^37))
                    Lib.Frac.frac_null
                    (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^47)
                      (- (Lib.Frac.frac_proj2 a^47)
                        (Lib.Frac.frac_proj2 b^37))))
                  Lib.Frac.frac_top)
                Lib.Frac.frac_top)))
(define-fun Lib.Frac.fpuAllowed ((a^48 Lib.Frac.T) (b^38 Lib.Frac.T)) Bool
            (ite (= a^48 b^38) true
              (ite
                (= a^48
                  (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^48)
                    (Lib.Frac.frac_proj2 a^48)))
                (and (= (Lib.Frac.frac_proj2 a^48) 1) (Lib.Frac.valid b^38))
                (ite (= a^48 Lib.Frac.frac_top) true false))))
(push 1)
; Initializing vars for proc_def Lib.Frac.weak_frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$35 Lib.Frac.T) (b$24 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$35 b$24))
                    (Lib.Frac.valid
                      (Lib.Frac.frame (Lib.Frac.comp a$35 b$24) b$24))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.idValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (Lib.Frac.valid Lib.Frac.id)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.frameValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$36 Lib.Frac.T) (b$25 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.frame a$36 b$25))
                    (and (Lib.Frac.valid a$36) (Lib.Frac.valid b$25))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.frameReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$37 Lib.Frac.T))
                  (=> (Lib.Frac.valid a$37)
                    (= (Lib.Frac.frame a$37 a$37) Lib.Frac.id)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$38 Lib.Frac.T))
                  (= (Lib.Frac.frame a$38 Lib.Frac.id) a$38))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$39 Lib.Frac.T) (b$26 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$39 b$26))
                    (= (Lib.Frac.frame (Lib.Frac.comp a$39 b$26) b$26) a$39)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$40 Lib.Frac.T) (b$27 Lib.Frac.T) (c$7 Lib.Frac.T))
                  (=>
                    (and
                      (and (Lib.Frac.fpuAllowed a$40 b$27)
                        (Lib.Frac.valid a$40))
                      (Lib.Frac.valid (Lib.Frac.comp a$40 c$7)))
                    (Lib.Frac.valid (Lib.Frac.comp b$27 c$7))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.fpuReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$41 Lib.Frac.T))
                  (=> (Lib.Frac.valid a$41) (Lib.Frac.fpuAllowed a$41 a$41)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$42 Lib.Frac.T) (b$28 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$42 b$28))
                    (and (Lib.Frac.valid a$42) (Lib.Frac.valid b$28))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$43 Lib.Frac.T))
                  (= (Lib.Frac.comp a$43 Lib.Frac.id) a$43))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$44 Lib.Frac.T) (b$29 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.frame a$44 b$29))
                    (= (Lib.Frac.comp (Lib.Frac.frame a$44 b$29) b$29) a$44)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$45 Lib.Frac.T) (b$30 Lib.Frac.T))
                  (= (Lib.Frac.comp a$45 b$30) (Lib.Frac.comp b$30 a$45)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Frac.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$46 Lib.Frac.T) (b$31 Lib.Frac.T) (c$8 Lib.Frac.T))
                  (= (Lib.Frac.comp (Lib.Frac.comp a$46 b$31) c$8)
                    (Lib.Frac.comp a$46 (Lib.Frac.comp b$31 c$8))))))
(check-sat)
(pop 1)
(pop 1)
; 
; 
; Entering module Lib.SetRA.
(declare-sort Lib.SetRA.X.T 0)
(declare-datatype
                   Lib.SetRA.T ( (Lib.SetRA.set_constr (Lib.SetRA.set_proj1
                   (Set Lib.SetRA.X.T))) (Lib.SetRA.set_top)))
(declare-const Lib.SetRA.id Lib.SetRA.T)
(assert
        (= Lib.SetRA.id
          (Lib.SetRA.set_constr ((as const (Set Lib.SetRA.X.T)) false))))
(define-fun Lib.SetRA.valid ((n^3 Lib.SetRA.T)) Bool
            (= n^3 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 n^3))))
(define-fun Lib.SetRA.comp ((a^57 Lib.SetRA.T) (b^45 Lib.SetRA.T))
            Lib.SetRA.T
            (ite
              (and (= a^57 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 a^57)))
                (= b^45 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 b^45))))
              (Lib.SetRA.set_constr
                (union (Lib.SetRA.set_proj1 a^57) (Lib.SetRA.set_proj1 b^45)))
              Lib.SetRA.set_top))
(define-fun Lib.SetRA.frame ((a^58 Lib.SetRA.T) (b^46 Lib.SetRA.T))
            Lib.SetRA.T
            (ite
              (and (= a^58 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 a^58)))
                (= b^46 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 b^46))))
              (ite
                (subset (Lib.SetRA.set_proj1 b^46)
                  (Lib.SetRA.set_proj1 a^58))
                a^58 Lib.SetRA.set_top)
              Lib.SetRA.set_top))
(define-fun Lib.SetRA.fpuAllowed ((a^59 Lib.SetRA.T) (b^47 Lib.SetRA.T)) Bool
            (ite
              (and (= a^59 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 a^59)))
                (= b^47 (Lib.SetRA.set_constr (Lib.SetRA.set_proj1 b^47))))
              (subset (Lib.SetRA.set_proj1 a^59) (Lib.SetRA.set_proj1 b^47))
              (ite
                (and (= a^59 Lib.SetRA.set_top) (= b^47 Lib.SetRA.set_top))
                true false)))
(push 1)
; Initializing vars for proc_def Lib.SetRA.weak_frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$47 Lib.SetRA.T) (b$32 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.comp a$47 b$32))
                    (Lib.SetRA.valid
                      (Lib.SetRA.frame (Lib.SetRA.comp a$47 b$32) b$32))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.idValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (Lib.SetRA.valid Lib.SetRA.id)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frame_comp_inv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$48 Lib.SetRA.T) (b$33 Lib.SetRA.T) (c$9 Lib.SetRA.T))
                  (= (Lib.SetRA.frame a$48 (Lib.SetRA.comp b$33 c$9))
                    (Lib.SetRA.frame (Lib.SetRA.frame a$48 b$33) c$9)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frameValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$49 Lib.SetRA.T) (b$34 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.frame a$49 b$34))
                    (and (Lib.SetRA.valid a$49) (Lib.SetRA.valid b$34))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$50 Lib.SetRA.T))
                  (= (Lib.SetRA.frame a$50 Lib.SetRA.id) a$50))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frameCompInv2
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$51 Lib.SetRA.T) (b$35 Lib.SetRA.T))
                  (=>
                    (and (= (Lib.SetRA.comp a$51 b$35) a$51)
                      (Lib.SetRA.valid a$51))
                    (= (Lib.SetRA.frame a$51 b$35) a$51)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frameCompInv0
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$52 Lib.SetRA.T) (b$36 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.comp a$52 b$36))
                    (= (Lib.SetRA.frame (Lib.SetRA.comp a$52 b$36) b$36)
                      (Lib.SetRA.comp a$52 b$36))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$53 Lib.SetRA.T) (b$37 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.frame a$53 b$37))
                    (= (Lib.SetRA.frame a$53 b$37) a$53)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$54 Lib.SetRA.T) (b$38 Lib.SetRA.T) (c$10 Lib.SetRA.T))
                  (=>
                    (and
                      (and (Lib.SetRA.fpuAllowed a$54 b$38)
                        (Lib.SetRA.valid a$54))
                      (Lib.SetRA.valid (Lib.SetRA.comp a$54 c$10)))
                    (Lib.SetRA.valid (Lib.SetRA.comp b$38 c$10))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.fpuReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$55 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid a$55)
                    (Lib.SetRA.fpuAllowed a$55 a$55)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$56 Lib.SetRA.T) (b$39 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.comp a$56 b$39))
                    (and (Lib.SetRA.valid a$56) (Lib.SetRA.valid b$39))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$57 Lib.SetRA.T))
                  (= (Lib.SetRA.comp a$57 Lib.SetRA.id) a$57))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$58 Lib.SetRA.T) (b$40 Lib.SetRA.T))
                  (=> (Lib.SetRA.valid (Lib.SetRA.frame a$58 b$40))
                    (= (Lib.SetRA.comp (Lib.SetRA.frame a$58 b$40) b$40)
                      a$58)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$59 Lib.SetRA.T) (b$41 Lib.SetRA.T))
                  (= (Lib.SetRA.comp a$59 b$41) (Lib.SetRA.comp b$41 a$59)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.SetRA.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$60 Lib.SetRA.T) (b$42 Lib.SetRA.T) (c$11 Lib.SetRA.T))
                  (= (Lib.SetRA.comp (Lib.SetRA.comp a$60 b$42) c$11)
                    (Lib.SetRA.comp a$60 (Lib.SetRA.comp b$42 c$11))))))
(check-sat)
(pop 1)
(pop 1)
; 
; 
; Entering module Lib.KeySetRA.
(declare-sort Lib.KeySetRA.X.T 0)
(declare-datatype
                   Lib.KeySetRA.T ( (Lib.KeySetRA.ksPair
                   (Lib.KeySetRA.ks_proj1 (Set Lib.KeySetRA.X.T))
                   (Lib.KeySetRA.ks_proj2 (Set Lib.KeySetRA.X.T)))
                   (Lib.KeySetRA.ksTop)))
(declare-const Lib.KeySetRA.id Lib.KeySetRA.T)
(assert
        (= Lib.KeySetRA.id
          (Lib.KeySetRA.ksPair ((as const (Set Lib.KeySetRA.X.T)) false)
            ((as const (Set Lib.KeySetRA.X.T)) false))))
(define-fun Lib.KeySetRA.valid ((n^4 Lib.KeySetRA.T)) Bool
            (ite
              (= n^4
                (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 n^4)
                  (Lib.KeySetRA.ks_proj2 n^4)))
              (subset (Lib.KeySetRA.ks_proj2 n^4)
                (Lib.KeySetRA.ks_proj1 n^4))
              false))
(define-fun Lib.KeySetRA.comp ((a^68 Lib.KeySetRA.T) (b^54 Lib.KeySetRA.T))
            Lib.KeySetRA.T
            (ite (= a^68 Lib.KeySetRA.id) b^54
              (ite (= b^54 Lib.KeySetRA.id) a^68
                (ite
                  (and
                    (= a^68
                      (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 a^68)
                        (Lib.KeySetRA.ks_proj2 a^68)))
                    (= b^54
                      (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 b^54)
                        (Lib.KeySetRA.ks_proj2 b^54))))
                  (ite
                    (and
                      (and (Lib.KeySetRA.valid a^68)
                        (Lib.KeySetRA.valid b^54))
                      (=
                        (intersection (Lib.KeySetRA.ks_proj1 a^68)
                          (Lib.KeySetRA.ks_proj1 b^54))
                        ((as const (Set Lib.KeySetRA.X.T)) false)))
                    (Lib.KeySetRA.ksPair
                      (union (Lib.KeySetRA.ks_proj1 a^68)
                        (Lib.KeySetRA.ks_proj1 b^54))
                      (union (Lib.KeySetRA.ks_proj2 a^68)
                        (Lib.KeySetRA.ks_proj2 b^54)))
                    Lib.KeySetRA.ksTop)
                  Lib.KeySetRA.ksTop))))
(define-fun Lib.KeySetRA.frame ((a^69 Lib.KeySetRA.T) (b^55 Lib.KeySetRA.T))
            Lib.KeySetRA.T
            (ite (= b^55 Lib.KeySetRA.id) a^69
              (ite
                (and
                  (= a^69
                    (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 a^69)
                      (Lib.KeySetRA.ks_proj2 a^69)))
                  (= b^55
                    (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 b^55)
                      (Lib.KeySetRA.ks_proj2 b^55))))
                (ite
                  (and
                    (and
                      (and (Lib.KeySetRA.valid a^69)
                        (Lib.KeySetRA.valid b^55))
                      (subset (Lib.KeySetRA.ks_proj1 b^55)
                        (Lib.KeySetRA.ks_proj1 a^69)))
                    (subset (Lib.KeySetRA.ks_proj2 b^55)
                      (Lib.KeySetRA.ks_proj2 a^69)))
                  (Lib.KeySetRA.ksPair
                    (intersection (Lib.KeySetRA.ks_proj1 a^69)
                      (complement (Lib.KeySetRA.ks_proj1 b^55)))
                    (intersection (Lib.KeySetRA.ks_proj2 a^69)
                      (complement (Lib.KeySetRA.ks_proj2 b^55))))
                  Lib.KeySetRA.ksTop)
                Lib.KeySetRA.ksTop)))
(define-fun Lib.KeySetRA.fpuAllowed ((a^70 Lib.KeySetRA.T)
            (b^56 Lib.KeySetRA.T)) Bool
            (ite (= a^70 b^56) true
              (ite
                (and
                  (= a^70
                    (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 a^70)
                      (Lib.KeySetRA.ks_proj2 a^70)))
                  (= b^56
                    (Lib.KeySetRA.ksPair (Lib.KeySetRA.ks_proj1 b^56)
                      (Lib.KeySetRA.ks_proj2 b^56))))
                (and
                  (and (Lib.KeySetRA.valid a^70) (Lib.KeySetRA.valid b^56))
                  (subset (Lib.KeySetRA.ks_proj1 b^56)
                    (Lib.KeySetRA.ks_proj1 a^70)))
                false)))
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.weak_frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$61 Lib.KeySetRA.T) (b$43 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid (Lib.KeySetRA.comp a$61 b$43))
                    (Lib.KeySetRA.valid
                      (Lib.KeySetRA.frame (Lib.KeySetRA.comp a$61 b$43) b$43))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.idValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (Lib.KeySetRA.valid Lib.KeySetRA.id)))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.frameValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$62 Lib.KeySetRA.T) (b$44 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid (Lib.KeySetRA.frame a$62 b$44))
                    (and (Lib.KeySetRA.valid a$62) (Lib.KeySetRA.valid b$44))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.frameReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$63 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid a$63)
                    (= (Lib.KeySetRA.frame a$63 a$63) Lib.KeySetRA.id)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$64 Lib.KeySetRA.T))
                  (= (Lib.KeySetRA.frame a$64 Lib.KeySetRA.id) a$64))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$65 Lib.KeySetRA.T) (b$45 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid (Lib.KeySetRA.comp a$65 b$45))
                    (=
                      (Lib.KeySetRA.frame (Lib.KeySetRA.comp a$65 b$45) b$45)
                      a$65)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall
                  ((a$66 Lib.KeySetRA.T) (b$46 Lib.KeySetRA.T)
                   (c$12 Lib.KeySetRA.T))
                  (=>
                    (and
                      (and (Lib.KeySetRA.fpuAllowed a$66 b$46)
                        (Lib.KeySetRA.valid a$66))
                      (Lib.KeySetRA.valid (Lib.KeySetRA.comp a$66 c$12)))
                    (Lib.KeySetRA.valid (Lib.KeySetRA.comp b$46 c$12))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.fpuReflexive
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$67 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid a$67)
                    (Lib.KeySetRA.fpuAllowed a$67 a$67)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$68 Lib.KeySetRA.T) (b$47 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid (Lib.KeySetRA.comp a$68 b$47))
                    (and (Lib.KeySetRA.valid a$68) (Lib.KeySetRA.valid b$47))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$69 Lib.KeySetRA.T))
                  (= (Lib.KeySetRA.comp a$69 Lib.KeySetRA.id) a$69))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$70 Lib.KeySetRA.T) (b$48 Lib.KeySetRA.T))
                  (=> (Lib.KeySetRA.valid (Lib.KeySetRA.frame a$70 b$48))
                    (=
                      (Lib.KeySetRA.comp (Lib.KeySetRA.frame a$70 b$48) b$48)
                      a$70)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$71 Lib.KeySetRA.T) (b$49 Lib.KeySetRA.T))
                  (= (Lib.KeySetRA.comp a$71 b$49)
                    (Lib.KeySetRA.comp b$49 a$71)))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.KeySetRA.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall
                  ((a$72 Lib.KeySetRA.T) (b$50 Lib.KeySetRA.T)
                   (c$13 Lib.KeySetRA.T))
                  (= (Lib.KeySetRA.comp (Lib.KeySetRA.comp a$72 b$50) c$13)
                    (Lib.KeySetRA.comp a$72 (Lib.KeySetRA.comp b$50 c$13))))))
(check-sat)
(pop 1)
(pop 1)
; End of Library
; 
; 
; ---- Starting Program ----
; 
; 
; Entering module $Program.
; 
; 
; Entering module $Program.Main.
(define-fun $Program.Main.f@HeapValid ((heap ($OwnHeap Int))) Bool
            (forall ((l $Loc)) (Lib.Nat.valid (select heap l))))
(define-fun $Program.Main.f@HeapChunkCompare ((x1 Int) (x2 Int)) Bool
            (Lib.Nat.valid (Lib.Nat.frame x2 x1)))
(declare-const $Program.Main.f@OwnHeap ($OwnHeap Int))
(assert ($Program.Main.f@HeapValid $Program.Main.f@OwnHeap))
(assert
        (forall ((loc $Loc))
                (= Lib.Nat.id (select $Program.Main.f@OwnHeap loc))))
(push 1)
; Initializing vars for proc_def $Program.Main.test
(declare-const x $Loc)
(declare-const k Int)
; Inhaling pre-conditions
(declare-const $Program.Main.f@OwnHeap$1 ($OwnHeap Int))
(assert ($Program.Main.f@HeapValid $Program.Main.f@OwnHeap$1))
(assert
        (forall ((l $Loc))
                (ite (= l x)
                  (= (select $Program.Main.f@OwnHeap$1 l)
                    (Lib.Nat.comp (select $Program.Main.f@OwnHeap l) k))
                  (= (select $Program.Main.f@OwnHeap$1 l)
                    (select $Program.Main.f@OwnHeap l)))))
(assert (> k 0))
; Executing body
(push 1)
(assert
        (not
          (Lib.Nat.fpuAllowed (select $Program.Main.f@OwnHeap$1 x) (- k 1))))
(check-sat)
(pop 1)
(declare-const $Program.Main.f@OwnHeap$2 ($OwnHeap Int))
(assert ($Program.Main.f@HeapValid $Program.Main.f@OwnHeap$2))
(assert
        (forall ((l $Loc))
                (ite (= l x) (= (select $Program.Main.f@OwnHeap$2 l) (- k 1))
                  (= (select $Program.Main.f@OwnHeap$2 l)
                    (select $Program.Main.f@OwnHeap$1 l)))))
; Exhaling post-conditions
(pop 1)

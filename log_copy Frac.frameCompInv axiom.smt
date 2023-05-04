(set-option :timeout 5000)
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
; Entering module Lib.Nat.
(declare-const Lib.Nat.id Int)
(assert (= Lib.Nat.id 0))
(define-fun Lib.Nat.valid ((n Int)) Bool (>= n 0))
(define-fun Lib.Nat.comp ((a^4 Int) (b^3 Int)) Int
            (ite (= a^4 Lib.Nat.id) b^3
              (ite (= b^3 Lib.Nat.id) a^4
                (ite (and (Lib.Nat.valid a^4) (Lib.Nat.valid b^3))
                  (+ a^4 b^3) (* -1 1)))))
(define-fun Lib.Nat.frame ((a^5 Int) (b^4 Int)) Int
            (ite (= b^4 Lib.Nat.id) a^5
              (ite (and (Lib.Nat.valid a^5) (Lib.Nat.valid b^4)) (- a^5 b^4)
                (* -1 1))))
(define-fun Lib.Nat.fpuAllowed ((a^6 Int) (b^5 Int)) Bool
            (forall ((c Int))
                    (=>
                      (and (and (Lib.Nat.valid a^6) (Lib.Nat.valid b^5))
                        (Lib.Nat.valid (Lib.Nat.comp a^6 c)))
                      (Lib.Nat.valid (Lib.Nat.comp b^5 c)))))
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
; Asserting axiom Lib.Nat.idValid
(assert (Lib.Nat.valid Lib.Nat.id))
(push 1)
; Initializing vars for proc_def Lib.Nat.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$1 Int)) (= (Lib.Nat.frame a$1 Lib.Nat.id) a$1))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.frameId
(assert (forall ((a$2 Int)) (= (Lib.Nat.frame a$2 Lib.Nat.id) a$2)))
(push 1)
; Initializing vars for proc_def Lib.Nat.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$3 Int) (b$1 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$3 b$1))
                    (= (Lib.Nat.frame (Lib.Nat.comp a$3 b$1) b$1) a$3)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.frameCompInv
(assert
        (forall ((a$4 Int) (b$2 Int))
                (=> (Lib.Nat.valid (Lib.Nat.comp a$4 b$2))
                  (= (Lib.Nat.frame (Lib.Nat.comp a$4 b$2) b$2) a$4))))
(push 1)
; Initializing vars for proc_def Lib.Nat.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$5 Int) (b$3 Int) (c$1 Int))
                  (=>
                    (and
                      (and
                        (and (Lib.Nat.fpuAllowed a$5 b$3)
                          (Lib.Nat.valid a$5))
                        (Lib.Nat.valid b$3))
                      (Lib.Nat.valid (Lib.Nat.comp a$5 c$1)))
                    (Lib.Nat.valid (Lib.Nat.comp b$3 c$1))))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.fpuValid
(assert
        (forall ((a$6 Int) (b$4 Int) (c$2 Int))
                (=>
                  (and
                    (and
                      (and (Lib.Nat.fpuAllowed a$6 b$4) (Lib.Nat.valid a$6))
                      (Lib.Nat.valid b$4))
                    (Lib.Nat.valid (Lib.Nat.comp a$6 c$2)))
                  (Lib.Nat.valid (Lib.Nat.comp b$4 c$2)))))
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
; Asserting axiom Lib.Nat.compValid
(assert
        (forall ((a$8 Int) (b$6 Int))
                (=> (Lib.Nat.valid (Lib.Nat.comp a$8 b$6))
                  (and (Lib.Nat.valid a$8) (Lib.Nat.valid b$6)))))
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
; Asserting axiom Lib.Nat.compId
(assert (forall ((a$10 Int)) (= (Lib.Nat.comp a$10 Lib.Nat.id) a$10)))
(push 1)
; Initializing vars for proc_def Lib.Nat.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$11 Int) (b$7 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.frame a$11 b$7))
                    (= (Lib.Nat.comp (Lib.Nat.frame a$11 b$7) b$7) a$11)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.compFrameInv
(assert
        (forall ((a$12 Int) (b$8 Int))
                (=> (Lib.Nat.valid (Lib.Nat.frame a$12 b$8))
                  (= (Lib.Nat.comp (Lib.Nat.frame a$12 b$8) b$8) a$12))))
(push 1)
; Initializing vars for proc_def Lib.Nat.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$13 Int) (b$9 Int))
                  (= (Lib.Nat.comp a$13 b$9) (Lib.Nat.comp b$9 a$13)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.compCommute
(assert
        (forall ((a$14 Int) (b$10 Int))
                (= (Lib.Nat.comp a$14 b$10) (Lib.Nat.comp b$10 a$14))))
(push 1)
; Initializing vars for proc_def Lib.Nat.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$15 Int) (b$11 Int) (c$3 Int))
                  (= (Lib.Nat.comp (Lib.Nat.comp a$15 b$11) c$3)
                    (Lib.Nat.comp a$15 (Lib.Nat.comp b$11 c$3))))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Nat.compAssoc
(assert
        (forall ((a$16 Int) (b$12 Int) (c$4 Int))
                (= (Lib.Nat.comp (Lib.Nat.comp a$16 b$12) c$4)
                  (Lib.Nat.comp a$16 (Lib.Nat.comp b$12 c$4)))))
; 
; 
; Entering module Lib.Auth.
(declare-sort Lib.Auth.M.T 0)
(declare-const Lib.Auth.M.id Lib.Auth.M.T)
(declare-fun Lib.Auth.M.comp (Lib.Auth.M.T Lib.Auth.M.T) Lib.Auth.M.T)
(declare-fun Lib.Auth.M.frame (Lib.Auth.M.T Lib.Auth.M.T) Lib.Auth.M.T)
(declare-fun Lib.Auth.M.valid (Lib.Auth.M.T) Bool)
(declare-fun Lib.Auth.M.fpuAllowed (Lib.Auth.M.T Lib.Auth.M.T) Bool)
; Asserting axiom idValid
(assert (Lib.Auth.M.valid Lib.Auth.M.id))
; Asserting axiom compAssoc
(assert
        (forall ((a$17 Lib.Auth.M.T) (b$13 Lib.Auth.M.T) (c$5 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp (Lib.Auth.M.comp a$17 b$13) c$5)
                  (Lib.Auth.M.comp a$17 (Lib.Auth.M.comp b$13 c$5)))))
; Asserting axiom compCommute
(assert
        (forall ((a$18 Lib.Auth.M.T) (b$14 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$18 b$14) (Lib.Auth.M.comp b$14 a$18))))
; Asserting axiom compId
(assert
        (forall ((a$19 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$19 Lib.Auth.M.id) a$19)))
; Asserting axiom compValid
(assert
        (forall ((a$20 Lib.Auth.M.T) (b$15 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$20 b$15))
                  (and (Lib.Auth.M.valid a$20) (Lib.Auth.M.valid b$15)))))
; Asserting axiom frameId
(assert
        (forall ((a$21 Lib.Auth.M.T))
                (= (Lib.Auth.M.frame a$21 Lib.Auth.M.id) a$21)))
; Asserting axiom frameCompInv
(assert
        (forall ((a$22 Lib.Auth.M.T) (b$16 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$22 b$16))
                  (= (Lib.Auth.M.frame (Lib.Auth.M.comp a$22 b$16) b$16)
                    a$22))))
; Asserting axiom compFrameInv
(assert
        (forall ((a$23 Lib.Auth.M.T) (b$17 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$23 b$17))
                  (= (Lib.Auth.M.comp (Lib.Auth.M.frame a$23 b$17) b$17)
                    a$23))))
; Asserting axiom fpuValid
(assert
        (forall ((a$24 Lib.Auth.M.T) (b$18 Lib.Auth.M.T) (c$6 Lib.Auth.M.T))
                (=>
                  (and
                    (and
                      (and (Lib.Auth.M.fpuAllowed a$24 b$18)
                        (Lib.Auth.M.valid a$24))
                      (Lib.Auth.M.valid b$18))
                    (Lib.Auth.M.valid (Lib.Auth.M.comp a$24 c$6)))
                  (Lib.Auth.M.valid (Lib.Auth.M.comp b$18 c$6)))))
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
(define-fun Lib.Auth.comp ((a^15 Lib.Auth.T) (b^12 Lib.Auth.T)) Lib.Auth.T
            (ite
              (and (= a^15 (Lib.Auth.frag (Lib.Auth.f_proj1 a^15)))
                (= b^12 (Lib.Auth.frag (Lib.Auth.f_proj1 b^12))))
              (Lib.Auth.frag
                (Lib.Auth.M.comp (Lib.Auth.f_proj1 a^15)
                  (Lib.Auth.f_proj1 b^12)))
              (ite
                (and (= a^15 (Lib.Auth.frag (Lib.Auth.f_proj1 a^15)))
                  (= b^12
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^12)
                      (Lib.Auth.af_proj2 b^12))))
                (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^12)
                  (Lib.Auth.M.comp (Lib.Auth.f_proj1 a^15)
                    (Lib.Auth.af_proj2 b^12)))
                (ite
                  (and
                    (= a^15
                      (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^15)
                        (Lib.Auth.af_proj2 a^15)))
                    (= b^12 (Lib.Auth.frag (Lib.Auth.f_proj1 b^12))))
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^15)
                    (Lib.Auth.M.comp (Lib.Auth.f_proj1 b^12)
                      (Lib.Auth.af_proj2 a^15)))
                  Lib.Auth.top))))
(define-fun Lib.Auth.frame ((a^16 Lib.Auth.T) (b^13 Lib.Auth.T)) Lib.Auth.T
            (ite
              (and (= a^16 (Lib.Auth.frag (Lib.Auth.f_proj1 a^16)))
                (= b^13 (Lib.Auth.frag (Lib.Auth.f_proj1 b^13))))
              (Lib.Auth.frag
                (Lib.Auth.M.frame (Lib.Auth.f_proj1 a^16)
                  (Lib.Auth.f_proj1 b^13)))
              (ite
                (and (= a^16 (Lib.Auth.frag (Lib.Auth.f_proj1 a^16)))
                  (= b^13
                    (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^13)
                      (Lib.Auth.af_proj2 b^13))))
                Lib.Auth.top
                (ite
                  (and
                    (= a^16
                      (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^16)
                        (Lib.Auth.af_proj2 a^16)))
                    (= b^13 (Lib.Auth.frag (Lib.Auth.f_proj1 b^13))))
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^16)
                    (Lib.Auth.M.frame (Lib.Auth.af_proj2 a^16)
                      (Lib.Auth.f_proj1 b^13)))
                  (ite
                    (and
                      (= a^16
                        (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^16)
                          (Lib.Auth.af_proj2 a^16)))
                      (= b^13
                        (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^13)
                          (Lib.Auth.af_proj2 b^13))))
                    (ite
                      (= (Lib.Auth.af_proj1 a^16) (Lib.Auth.af_proj1 b^13))
                      (Lib.Auth.frag
                        (Lib.Auth.M.frame (Lib.Auth.af_proj2 a^16)
                          (Lib.Auth.af_proj2 b^13)))
                      Lib.Auth.top)
                    Lib.Auth.top)))))
(define-fun Lib.Auth.fpuAllowed ((a^17 Lib.Auth.T) (b^14 Lib.Auth.T)) Bool
            (ite
              (and
                (= a^17
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 a^17)
                    (Lib.Auth.af_proj2 a^17)))
                (= b^14
                  (Lib.Auth.auth_frag (Lib.Auth.af_proj1 b^14)
                    (Lib.Auth.af_proj2 b^14))))
              (and
                (and
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.af_proj1 b^14)
                      (Lib.Auth.af_proj1 a^17)))
                  (Lib.Auth.M.valid
                    (Lib.Auth.M.frame (Lib.Auth.af_proj2 b^14)
                      (Lib.Auth.af_proj2 a^17))))
                (Lib.Auth.M.valid
                  (Lib.Auth.M.frame
                    (Lib.Auth.M.frame (Lib.Auth.af_proj1 b^14)
                      (Lib.Auth.af_proj1 a^17))
                    (Lib.Auth.M.frame (Lib.Auth.af_proj2 b^14)
                      (Lib.Auth.af_proj2 a^17)))))
              false))
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
; Asserting axiom Lib.Auth.idValid
(assert (Lib.Auth.valid Lib.Auth.id))
(push 1)
; Initializing vars for proc_def Lib.Auth.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$25 Lib.Auth.T))
                  (= (Lib.Auth.frame a$25 Lib.Auth.id) a$25))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.frameId
(assert
        (forall ((a$26 Lib.Auth.T))
                (= (Lib.Auth.frame a$26 Lib.Auth.id) a$26)))
(push 1)
; Initializing vars for proc_def Lib.Auth.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$27 Lib.Auth.T) (b$19 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$27 b$19))
                    (= (Lib.Auth.frame (Lib.Auth.comp a$27 b$19) b$19) a$27)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.frameCompInv
(assert
        (forall ((a$28 Lib.Auth.T) (b$20 Lib.Auth.T))
                (=> (Lib.Auth.valid (Lib.Auth.comp a$28 b$20))
                  (= (Lib.Auth.frame (Lib.Auth.comp a$28 b$20) b$20) a$28))))
(push 1)
; Initializing vars for proc_def Lib.Auth.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$29 Lib.Auth.T) (b$21 Lib.Auth.T) (c$7 Lib.Auth.T))
                  (=>
                    (and
                      (and
                        (and (Lib.Auth.fpuAllowed a$29 b$21)
                          (Lib.Auth.valid a$29))
                        (Lib.Auth.valid b$21))
                      (Lib.Auth.valid (Lib.Auth.comp a$29 c$7)))
                    (Lib.Auth.valid (Lib.Auth.comp b$21 c$7))))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.fpuValid
(assert
        (forall ((a$30 Lib.Auth.T) (b$22 Lib.Auth.T) (c$8 Lib.Auth.T))
                (=>
                  (and
                    (and
                      (and (Lib.Auth.fpuAllowed a$30 b$22)
                        (Lib.Auth.valid a$30))
                      (Lib.Auth.valid b$22))
                    (Lib.Auth.valid (Lib.Auth.comp a$30 c$8)))
                  (Lib.Auth.valid (Lib.Auth.comp b$22 c$8)))))
(push 1)
; Initializing vars for proc_def Lib.Auth.compValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$31 Lib.Auth.T) (b$23 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$31 b$23))
                    (and (Lib.Auth.valid a$31) (Lib.Auth.valid b$23))))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.compValid
(assert
        (forall ((a$32 Lib.Auth.T) (b$24 Lib.Auth.T))
                (=> (Lib.Auth.valid (Lib.Auth.comp a$32 b$24))
                  (and (Lib.Auth.valid a$32) (Lib.Auth.valid b$24)))))
(push 1)
; Initializing vars for proc_def Lib.Auth.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$33 Lib.Auth.T))
                  (= (Lib.Auth.comp a$33 Lib.Auth.id) a$33))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.compId
(assert
        (forall ((a$34 Lib.Auth.T))
                (= (Lib.Auth.comp a$34 Lib.Auth.id) a$34)))
(push 1)
; Initializing vars for proc_def Lib.Auth.compFrameInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$35 Lib.Auth.T) (b$25 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.frame a$35 b$25))
                    (= (Lib.Auth.comp (Lib.Auth.frame a$35 b$25) b$25) a$35)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.compFrameInv
(assert
        (forall ((a$36 Lib.Auth.T) (b$26 Lib.Auth.T))
                (=> (Lib.Auth.valid (Lib.Auth.frame a$36 b$26))
                  (= (Lib.Auth.comp (Lib.Auth.frame a$36 b$26) b$26) a$36))))
(push 1)
; Initializing vars for proc_def Lib.Auth.compCommute
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$37 Lib.Auth.T) (b$27 Lib.Auth.T))
                  (= (Lib.Auth.comp a$37 b$27) (Lib.Auth.comp b$27 a$37)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.compCommute
(assert
        (forall ((a$38 Lib.Auth.T) (b$28 Lib.Auth.T))
                (= (Lib.Auth.comp a$38 b$28) (Lib.Auth.comp b$28 a$38))))
(push 1)
; Initializing vars for proc_def Lib.Auth.compAssoc
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$39 Lib.Auth.T) (b$29 Lib.Auth.T) (c$9 Lib.Auth.T))
                  (= (Lib.Auth.comp (Lib.Auth.comp a$39 b$29) c$9)
                    (Lib.Auth.comp a$39 (Lib.Auth.comp b$29 c$9))))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Auth.compAssoc
(assert
        (forall ((a$40 Lib.Auth.T) (b$30 Lib.Auth.T) (c$10 Lib.Auth.T))
                (= (Lib.Auth.comp (Lib.Auth.comp a$40 b$30) c$10)
                  (Lib.Auth.comp a$40 (Lib.Auth.comp b$30 c$10)))))
; 
; 
; Entering module Lib.Frac.
(declare-sort Lib.Frac.X.T 0)
(declare-datatype
                   Lib.Frac.T ( (Lib.Frac.frac_null) (Lib.Frac.frac_chunk
                   (Lib.Frac.frac_proj1 Lib.Frac.X.T) (Lib.Frac.frac_proj2
                   Int)) (Lib.Frac.frac_top)))
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
(define-fun Lib.Frac.comp ((a^22 Lib.Frac.T) (b^18 Lib.Frac.T)) Lib.Frac.T
            (ite (= a^22 Lib.Frac.frac_null) b^18
              (ite (= b^18 Lib.Frac.frac_null) a^22
                (ite (and (Lib.Frac.valid a^22) (Lib.Frac.valid b^18))
                  (ite
                    (= (Lib.Frac.frac_proj1 a^22) (Lib.Frac.frac_proj1 b^18))
                    (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^22)
                      (+ (Lib.Frac.frac_proj2 a^22)
                        (Lib.Frac.frac_proj2 b^18)))
                    Lib.Frac.frac_top)
                  Lib.Frac.frac_top))))
(define-fun Lib.Frac.frame ((a^23 Lib.Frac.T) (b^19 Lib.Frac.T)) Lib.Frac.T
            (ite (= b^19 Lib.Frac.frac_null) a^23
              (ite
                (and
                  (and
                    (and
                      (= a^23
                        (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^23)
                          (Lib.Frac.frac_proj2 a^23)))
                      (= b^19
                        (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 b^19)
                          (Lib.Frac.frac_proj2 b^19))))
                    (Lib.Frac.valid a^23))
                  (Lib.Frac.valid b^19))
                (ite
                  (= (Lib.Frac.frac_proj1 a^23) (Lib.Frac.frac_proj1 b^19))
                  (ite
                    (= (Lib.Frac.frac_proj2 a^23) (Lib.Frac.frac_proj2 b^19))
                    Lib.Frac.frac_null
                    (Lib.Frac.frac_chunk (Lib.Frac.frac_proj1 a^23)
                      (- (Lib.Frac.frac_proj2 a^23)
                        (Lib.Frac.frac_proj2 b^19))))
                  Lib.Frac.frac_top)
                Lib.Frac.frac_top)))
(define-fun Lib.Frac.fpuAllowed ((a^24 Lib.Frac.T) (b^20 Lib.Frac.T)) Bool
            (forall ((c$11 Lib.Frac.T))
                    (=>
                      (and (and (Lib.Frac.valid a^24) (Lib.Frac.valid b^20))
                        (Lib.Frac.valid (Lib.Frac.comp a^24 c$11)))
                      (Lib.Frac.valid (Lib.Frac.comp b^20 c$11)))))
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
; Asserting axiom Lib.Frac.idValid
(assert (Lib.Frac.valid Lib.Frac.id))
(push 1)
; Initializing vars for proc_def Lib.Frac.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$41 Lib.Frac.T))
                  (= (Lib.Frac.frame a$41 Lib.Frac.id) a$41))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Frac.frameId
(assert
        (forall ((a$42 Lib.Frac.T))
                (= (Lib.Frac.frame a$42 Lib.Frac.id) a$42)))
(push 1)
; Initializing vars for proc_def Lib.Frac.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$43 Lib.Frac.T) (b$31 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$43 b$31))
                    (= (Lib.Frac.frame (Lib.Frac.comp a$43 b$31) b$31) a$43)))))
(check-sat)
(pop 1)
(pop 1)
; Asserting axiom Lib.Frac.frameCompInv

; commenting out the below axiom works. Leaving it in causes timeout
(assert
        (forall ((a$44 Lib.Frac.T) (b$32 Lib.Frac.T))
                (=> (Lib.Frac.valid (Lib.Frac.comp a$44 b$32))
                  (= (Lib.Frac.frame (Lib.Frac.comp a$44 b$32) b$32) a$44))))
(push 1)
; Initializing vars for proc_def Lib.Frac.fpuValid
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$45 Lib.Frac.T) (b$33 Lib.Frac.T) (c$12 Lib.Frac.T))
                  (=>
                    (and
                      (and
                        (and (Lib.Frac.fpuAllowed a$45 b$33)
                          (Lib.Frac.valid a$45))
                        (Lib.Frac.valid b$33))
                      (Lib.Frac.valid (Lib.Frac.comp a$45 c$12)))
                    (Lib.Frac.valid (Lib.Frac.comp b$33 c$12))))))
(check-sat)

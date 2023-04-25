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
(declare-sort Lib.Type.T 0)
(declare-sort Lib.ResourceAlgebra.T 0)
(declare-const Lib.ResourceAlgebra.id Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.comp (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.frame (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Lib.ResourceAlgebra.T)
(declare-fun Lib.ResourceAlgebra.valid (Lib.ResourceAlgebra.T) Bool)
(declare-fun Lib.ResourceAlgebra.fpuAllowed (Lib.ResourceAlgebra.T
             Lib.ResourceAlgebra.T) Bool)
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
(push 1)
; Initializing vars for proc_def Lib.Nat.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$2 Int) (b$1 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$2 b$1))
                    (= (Lib.Nat.frame (Lib.Nat.comp a$2 b$1) b$1) a$2)))))
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
          (forall ((a$3 Int) (b$2 Int) (c$1 Int))
                  (=>
                    (and
                      (and
                        (and (Lib.Nat.fpuAllowed a$3 b$2)
                          (Lib.Nat.valid a$3))
                        (Lib.Nat.valid b$2))
                      (Lib.Nat.valid (Lib.Nat.comp a$3 c$1)))
                    (Lib.Nat.valid (Lib.Nat.comp b$2 c$1))))))
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
          (forall ((a$4 Int) (b$3 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.comp a$4 b$3))
                    (and (Lib.Nat.valid a$4) (Lib.Nat.valid b$3))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Nat.compId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert (not (forall ((a$5 Int)) (= (Lib.Nat.comp a$5 Lib.Nat.id) a$5))))
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
          (forall ((a$6 Int) (b$4 Int))
                  (=> (Lib.Nat.valid (Lib.Nat.frame a$6 b$4))
                    (= (Lib.Nat.comp (Lib.Nat.frame a$6 b$4) b$4) a$6)))))
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
          (forall ((a$7 Int) (b$5 Int))
                  (= (Lib.Nat.comp a$7 b$5) (Lib.Nat.comp b$5 a$7)))))
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
          (forall ((a$8 Int) (b$6 Int) (c$2 Int))
                  (= (Lib.Nat.comp (Lib.Nat.comp a$8 b$6) c$2)
                    (Lib.Nat.comp a$8 (Lib.Nat.comp b$6 c$2))))))
(check-sat)
(pop 1)
(pop 1)
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
        (forall ((a$9 Lib.Auth.M.T) (b$7 Lib.Auth.M.T) (c$3 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp (Lib.Auth.M.comp a$9 b$7) c$3)
                  (Lib.Auth.M.comp a$9 (Lib.Auth.M.comp b$7 c$3)))))
; Asserting axiom compCommute
(assert
        (forall ((a$10 Lib.Auth.M.T) (b$8 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$10 b$8) (Lib.Auth.M.comp b$8 a$10))))
; Asserting axiom compId
(assert
        (forall ((a$11 Lib.Auth.M.T))
                (= (Lib.Auth.M.comp a$11 Lib.Auth.M.id) a$11)))
; Asserting axiom compValid
(assert
        (forall ((a$12 Lib.Auth.M.T) (b$9 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$12 b$9))
                  (and (Lib.Auth.M.valid a$12) (Lib.Auth.M.valid b$9)))))
; Asserting axiom frameId
(assert
        (forall ((a$13 Lib.Auth.M.T))
                (= (Lib.Auth.M.frame a$13 Lib.Auth.M.id) a$13)))
; Asserting axiom frameCompInv
(assert
        (forall ((a$14 Lib.Auth.M.T) (b$10 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.comp a$14 b$10))
                  (= (Lib.Auth.M.frame (Lib.Auth.M.comp a$14 b$10) b$10)
                    a$14))))
; Asserting axiom compFrameInv
(assert
        (forall ((a$15 Lib.Auth.M.T) (b$11 Lib.Auth.M.T))
                (=> (Lib.Auth.M.valid (Lib.Auth.M.frame a$15 b$11))
                  (= (Lib.Auth.M.comp (Lib.Auth.M.frame a$15 b$11) b$11)
                    a$15))))
; Asserting axiom fpuValid
(assert
        (forall ((a$16 Lib.Auth.M.T) (b$12 Lib.Auth.M.T) (c$4 Lib.Auth.M.T))
                (=>
                  (and
                    (and
                      (and (Lib.Auth.M.fpuAllowed a$16 b$12)
                        (Lib.Auth.M.valid a$16))
                      (Lib.Auth.M.valid b$12))
                    (Lib.Auth.M.valid (Lib.Auth.M.comp a$16 c$4)))
                  (Lib.Auth.M.valid (Lib.Auth.M.comp b$12 c$4)))))
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
(push 1)
; Initializing vars for proc_def Lib.Auth.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$17 Lib.Auth.T))
                  (= (Lib.Auth.frame a$17 Lib.Auth.id) a$17))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
; Initializing vars for proc_def Lib.Auth.frameCompInv
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$18 Lib.Auth.T) (b$13 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$18 b$13))
                    (= (Lib.Auth.frame (Lib.Auth.comp a$18 b$13) b$13) a$18)))))
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
          (forall ((a$19 Lib.Auth.T) (b$14 Lib.Auth.T) (c$5 Lib.Auth.T))
                  (=>
                    (and
                      (and
                        (and (Lib.Auth.fpuAllowed a$19 b$14)
                          (Lib.Auth.valid a$19))
                        (Lib.Auth.valid b$14))
                      (Lib.Auth.valid (Lib.Auth.comp a$19 c$5)))
                    (Lib.Auth.valid (Lib.Auth.comp b$14 c$5))))))
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
          (forall ((a$20 Lib.Auth.T) (b$15 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.comp a$20 b$15))
                    (and (Lib.Auth.valid a$20) (Lib.Auth.valid b$15))))))
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
          (forall ((a$21 Lib.Auth.T))
                  (= (Lib.Auth.comp a$21 Lib.Auth.id) a$21))))
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
          (forall ((a$22 Lib.Auth.T) (b$16 Lib.Auth.T))
                  (=> (Lib.Auth.valid (Lib.Auth.frame a$22 b$16))
                    (= (Lib.Auth.comp (Lib.Auth.frame a$22 b$16) b$16) a$22)))))
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
          (forall ((a$23 Lib.Auth.T) (b$17 Lib.Auth.T))
                  (= (Lib.Auth.comp a$23 b$17) (Lib.Auth.comp b$17 a$23)))))
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
          (forall ((a$24 Lib.Auth.T) (b$18 Lib.Auth.T) (c$6 Lib.Auth.T))
                  (= (Lib.Auth.comp (Lib.Auth.comp a$24 b$18) c$6)
                    (Lib.Auth.comp a$24 (Lib.Auth.comp b$18 c$6))))))
(check-sat)
(pop 1)
(pop 1)
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
            (forall ((c$7 Lib.Frac.T))
                    (=>
                      (and (and (Lib.Frac.valid a^24) (Lib.Frac.valid b^20))
                        (Lib.Frac.valid (Lib.Frac.comp a^24 c$7)))
                      (Lib.Frac.valid (Lib.Frac.comp b^20 c$7)))))
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
; Initializing vars for proc_def Lib.Frac.frameId
; Inhaling pre-conditions
; Executing body
; Exhaling post-conditions
(push 1)
(assert
        (not
          (forall ((a$25 Lib.Frac.T))
                  (= (Lib.Frac.frame a$25 Lib.Frac.id) a$25))))
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
          (forall ((a$26 Lib.Frac.T) (b$19 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$26 b$19))
                    (= (Lib.Frac.frame (Lib.Frac.comp a$26 b$19) b$19) a$26)))))
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
          (forall ((a$27 Lib.Frac.T) (b$20 Lib.Frac.T) (c$8 Lib.Frac.T))
                  (=>
                    (and
                      (and
                        (and (Lib.Frac.fpuAllowed a$27 b$20)
                          (Lib.Frac.valid a$27))
                        (Lib.Frac.valid b$20))
                      (Lib.Frac.valid (Lib.Frac.comp a$27 c$8)))
                    (Lib.Frac.valid (Lib.Frac.comp b$20 c$8))))))
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
          (forall ((a$28 Lib.Frac.T) (b$21 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.comp a$28 b$21))
                    (and (Lib.Frac.valid a$28) (Lib.Frac.valid b$21))))))
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
          (forall ((a$29 Lib.Frac.T))
                  (= (Lib.Frac.comp a$29 Lib.Frac.id) a$29))))
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
          (forall ((a$30 Lib.Frac.T) (b$22 Lib.Frac.T))
                  (=> (Lib.Frac.valid (Lib.Frac.frame a$30 b$22))
                    (= (Lib.Frac.comp (Lib.Frac.frame a$30 b$22) b$22) a$30)))))
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
          (forall ((a$31 Lib.Frac.T) (b$23 Lib.Frac.T))
                  (= (Lib.Frac.comp a$31 b$23) (Lib.Frac.comp b$23 a$31)))))
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
          (forall ((a$32 Lib.Frac.T) (b$24 Lib.Frac.T) (c$9 Lib.Frac.T))
                  (= (Lib.Frac.comp (Lib.Frac.comp a$32 b$24) c$9)
                    (Lib.Frac.comp a$32 (Lib.Frac.comp b$24 c$9))))))
(check-sat)
(pop 1)
(pop 1)
; End of Library
; 
; 
; ---- Starting Program ----
(declare-sort $Program.IArray.T 0)
(declare-fun $Program.IArray.loc ($Program.IArray.T Int) $Loc)
(declare-fun $Program.IArray.len ($Program.IArray.T) Int)
(declare-fun $Program.IArray.first ($Loc) $Program.IArray.T)
(declare-fun $Program.IArray.second ($Loc) Int)
(declare-sort $Program.ArrayMax.M.T 0)
(declare-fun $Program.ArrayMax.M.loc ($Program.ArrayMax.M.T Int) $Loc)
(declare-fun $Program.ArrayMax.M.len ($Program.ArrayMax.M.T) Int)
(declare-fun $Program.ArrayMax.M.first ($Loc) $Program.ArrayMax.M.T)
(declare-fun $Program.ArrayMax.M.second ($Loc) Int)
; Asserting axiom all_diff
(assert
        (forall ((a$33 $Program.ArrayMax.M.T) (i$1 Int))
                (and
                  (=
                    ($Program.ArrayMax.M.first
                      ($Program.ArrayMax.M.loc a$33 i$1))
                    a$33)
                  (=
                    ($Program.ArrayMax.M.second
                      ($Program.ArrayMax.M.loc a$33 i$1))
                    i$1))))
; Asserting axiom len_nonneg
(assert
        (forall ((a$34 $Program.ArrayMax.M.T))
                (>= ($Program.ArrayMax.M.len a$34) 0)))
(declare-const $Program.ArrayMax.value@OwnHeap
             ($OwnHeap ($FracHeapChunk Int)))
(assert ($IntFracHeapValid $Program.ArrayMax.value@OwnHeap))
(assert
        (forall ((loc $Loc))
                (= (as $FracHeapNull ($FracHeapChunk Int))
                  (select $Program.ArrayMax.value@OwnHeap loc))))
(declare-const $Program.ArrayMax.x Int)
(assert (= $Program.ArrayMax.x 4))
(declare-datatype
                   $Program.ArrayMax.arr$Pred (
                   ($Program.ArrayMax.arr$Pred$Constr
                   ($Program.ArrayMax.arr$Pred$Arg0 $Program.ArrayMax.M.T)
                   ($Program.ArrayMax.arr$Pred$Arg1 (Array Int Int)))))
(declare-const $Program.ArrayMax.arr$Pred$Heap
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (= (select $Program.ArrayMax.arr$Pred$Heap $index) 0)))
(declare-datatype
                   $Program.ArrayMax.is_max$Pred (
                   ($Program.ArrayMax.is_max$Pred$Constr
                   ($Program.ArrayMax.is_max$Pred$Arg0 Int)
                   ($Program.ArrayMax.is_max$Pred$Arg1 (Array Int Int))
                   ($Program.ArrayMax.is_max$Pred$Arg2 Int))))
(declare-const $Program.ArrayMax.is_max$Pred$Heap
             ($PredHeap $Program.ArrayMax.is_max$Pred))
(assert
        (forall (($index $Program.ArrayMax.is_max$Pred))
                (= (select $Program.ArrayMax.is_max$Pred$Heap $index) 0)))
(push 1)
; Initializing vars for proc_def $Program.ArrayMax.max
(declare-const a^36 $Program.ArrayMax.M.T)
(declare-const m^2 (Array Int Int))
(declare-const x Int)
; Inhaling pre-conditions
(declare-const $Program.ArrayMax.arr$Pred$Heap$1
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$1 $index) 0)))
(assert
        (forall ((x0 $Program.ArrayMax.M.T) (x1 (Array Int Int)))
                (ite (and (= x0 a^36) (= x1 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$1
                      ($Program.ArrayMax.arr$Pred$Constr x0 x1))
                    (+ 1
                      (select $Program.ArrayMax.arr$Pred$Heap
                        ($Program.ArrayMax.arr$Pred$Constr x0 x1))))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$1
                      ($Program.ArrayMax.arr$Pred$Constr x0 x1))
                    (select $Program.ArrayMax.arr$Pred$Heap
                      ($Program.ArrayMax.arr$Pred$Constr x0 x1))))))
; Executing body
(declare-const z Int)
(declare-const x$1 Int)
(assert (= x$1 (* -1 1)))
(declare-const y Int)
(declare-const x$2 Int)
(assert (= x$2 0))
(declare-const y$1 Int)
(assert (= y$1 (- ($Program.ArrayMax.M.len a^36) 1)))
; Exhaling loop invariants in current state

(declare-const $Program.ArrayMax.arr$Pred$Heap$2
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$2 $index) 0)))
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (<= 1
              (select $Program.ArrayMax.arr$Pred$Heap$1
                ($Program.ArrayMax.arr$Pred$Constr a^36 m^2))))))
(check-sat)
(pop 1)
(assert
        (forall ((x0$1 $Program.ArrayMax.M.T) (x1$1 (Array Int Int)))
                (ite (and (= x0$1 a^36) (= x1$1 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$2
                      ($Program.ArrayMax.arr$Pred$Constr x0$1 x1$1))
                    (-
                      (select $Program.ArrayMax.arr$Pred$Heap$1
                        ($Program.ArrayMax.arr$Pred$Constr x0$1 x1$1))
                      1))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$2
                      ($Program.ArrayMax.arr$Pred$Constr x0$1 x1$1))
                    (select $Program.ArrayMax.arr$Pred$Heap$1
                      ($Program.ArrayMax.arr$Pred$Constr x0$1 x1$1))))))
(push 1)
(assert (not (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (<= 0 x$2))))
(check-sat)
(pop 1)
(push 1)
(assert (not (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (<= x$2 y$1))))
(check-sat)
(pop 1)
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (< y$1 ($Program.ArrayMax.M.len a^36)))))
(check-sat)
(pop 1)
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (forall ((i$2 Int))
                    (or
                      (=>
                        (or (and (<= 0 i$2) (< i$2 x$2))
                          (and (< y$1 i$2)
                            (< i$2 ($Program.ArrayMax.M.len a^36))))
                        (< (select m^2 i$2) (select m^2 x$2)))
                      (=>
                        (or (and (<= 0 i$2) (< i$2 x$2))
                          (and (< y$1 i$2)
                            (< i$2 ($Program.ArrayMax.M.len a^36))))
                        (<= (select m^2 i$2) (select m^2 y$1))))))))
(check-sat)
(pop 1)
; Havoc-ing loop vars

(declare-const y$2 Int)
(declare-const x$3 Int)
; Checking loop

(push 1)
; Resetting all heaps

(declare-const $Program.ArrayMax.arr$Pred$Heap$3
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$3 $index) 0)))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (= (select $Program.ArrayMax.arr$Pred$Heap$3 $index) 0)))
(declare-const $Program.ArrayMax.is_max$Pred$Heap$1
             ($PredHeap $Program.ArrayMax.is_max$Pred))
(assert
        (forall (($index $Program.ArrayMax.is_max$Pred))
                (>= (select $Program.ArrayMax.is_max$Pred$Heap$1 $index) 0)))
(assert
        (forall (($index $Program.ArrayMax.is_max$Pred))
                (= (select $Program.ArrayMax.is_max$Pred$Heap$1 $index) 0)))
(declare-const $Program.ArrayMax.value@OwnHeap$1
             ($OwnHeap ($FracHeapChunk Int)))
(assert ($IntFracHeapValid $Program.ArrayMax.value@OwnHeap$1))
(assert
        (forall ((l $Loc))
                (= (as $FracHeapNull ($FracHeapChunk Int))
                  (select $Program.ArrayMax.value@OwnHeap$1 l))))
; Inhaling invariants inside loop
(declare-const $Program.ArrayMax.arr$Pred$Heap$4
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$4 $index) 0)))
(assert
        (forall ((x0$2 $Program.ArrayMax.M.T) (x1$2 (Array Int Int)))
                (ite (and (= x0$2 a^36) (= x1$2 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$4
                      ($Program.ArrayMax.arr$Pred$Constr x0$2 x1$2))
                    (+ 1
                      (select $Program.ArrayMax.arr$Pred$Heap$3
                        ($Program.ArrayMax.arr$Pred$Constr x0$2 x1$2))))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$4
                      ($Program.ArrayMax.arr$Pred$Constr x0$2 x1$2))
                    (select $Program.ArrayMax.arr$Pred$Heap$3
                      ($Program.ArrayMax.arr$Pred$Constr x0$2 x1$2))))))
(assert (<= 0 x$3))
(assert (<= x$3 y$2))
(assert (< y$2 ($Program.ArrayMax.M.len a^36)))
(assert
        (forall ((i$3 Int))
                (or
                  (=>
                    (or (and (<= 0 i$3) (< i$3 x$3))
                      (and (< y$2 i$3)
                        (< i$3 ($Program.ArrayMax.M.len a^36))))
                    (< (select m^2 i$3) (select m^2 x$3)))
                  (=>
                    (or (and (<= 0 i$3) (< i$3 x$3))
                      (and (< y$2 i$3)
                        (< i$3 ($Program.ArrayMax.M.len a^36))))
                    (<= (select m^2 i$3) (select m^2 y$2))))))
(assert (not (= x$3 y$2)))
(declare-const $Program.ArrayMax.arr$Pred$Heap$5
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$5 $index) 0)))
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (<= 1
              (select $Program.ArrayMax.arr$Pred$Heap$4
                ($Program.ArrayMax.arr$Pred$Constr a^36 m^2))))))
(check-sat)
(pop 1)
(assert
        (forall ((x0$3 $Program.ArrayMax.M.T) (x1$3 (Array Int Int)))
                (ite (and (= x0$3 a^36) (= x1$3 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$5
                      ($Program.ArrayMax.arr$Pred$Constr x0$3 x1$3))
                    (-
                      (select $Program.ArrayMax.arr$Pred$Heap$4
                        ($Program.ArrayMax.arr$Pred$Constr x0$3 x1$3))
                      1))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$5
                      ($Program.ArrayMax.arr$Pred$Constr x0$3 x1$3))
                    (select $Program.ArrayMax.arr$Pred$Heap$4
                      ($Program.ArrayMax.arr$Pred$Constr x0$3 x1$3))))))
(declare-const $Program.ArrayMax.value@OwnHeap$2
             ($OwnHeap ($FracHeapChunk Int)))
(assert ($IntFracHeapValid $Program.ArrayMax.value@OwnHeap$2))
(assert
        (forall ((j Int))
                (=> (and (<= 0 j) (< j ($Program.ArrayMax.M.len a^36)))
                  (=
                    (select $Program.ArrayMax.value@OwnHeap$2
                      ($Program.ArrayMax.M.loc a^36 j))
                    ($IntFracChunkAdd
                      (select $Program.ArrayMax.value@OwnHeap$1
                        ($Program.ArrayMax.M.loc a^36 j))
                      ($FracChunkConstr (select m^2 j) 1))))))
(assert
        (forall ((l $Loc))
                (or
                  (exists ((j Int))
                          (and (= l ($Program.ArrayMax.M.loc a^36 j))
                            (and (<= 0 j)
                              (< j ($Program.ArrayMax.M.len a^36)))))
                  (= (select $Program.ArrayMax.value@OwnHeap$2 l)
                    (select $Program.ArrayMax.value@OwnHeap$1 l)))))
(declare-const tmp1 Int)
(declare-const tmp1$1 Int)
; Checking field read permission

(push 1)
(assert
        (not
          (< 0
            ($FracOwn
              (select $Program.ArrayMax.value@OwnHeap$2
                ($Program.ArrayMax.M.loc a^36 x$3))))))
(check-sat)
(pop 1)
(assert
        (= tmp1$1
          ($FracVal
            (select $Program.ArrayMax.value@OwnHeap$2
              ($Program.ArrayMax.M.loc a^36 x$3)))))
(declare-const tmp2 Int)
(declare-const tmp2$1 Int)
; Checking field read permission

(push 1)
(assert
        (not
          (< 0
            ($FracOwn
              (select $Program.ArrayMax.value@OwnHeap$2
                ($Program.ArrayMax.M.loc a^36 y$2))))))
(check-sat)
(pop 1)
(assert
        (= tmp2$1
          ($FracVal
            (select $Program.ArrayMax.value@OwnHeap$2
              ($Program.ArrayMax.M.loc a^36 y$2)))))
(declare-const x$4 Int)
(assert (= x$4 (+ x$4 1)))
(declare-const y$3 Int)
(assert (= y$3 (- y$3 1)))
; Unifying conditional branches

(declare-const x$5 Int)
(declare-const y$4 Int)
(assert (=> (<= tmp1$1 tmp2$1) (= x$4 x$5)))
(assert (=> (not (<= tmp1$1 tmp2$1)) (= x$3 x$5)))
(assert (=> (<= tmp1$1 tmp2$1) (= y$2 y$4)))
(assert (=> (not (<= tmp1$1 tmp2$1)) (= y$3 y$4)))
; Finished unifying conditional branches

; Exhaling body of predicate
(declare-const $Program.ArrayMax.value@OwnHeap$3
             ($OwnHeap ($FracHeapChunk Int)))
(assert ($IntFracHeapValid $Program.ArrayMax.value@OwnHeap$3))
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (forall ((j$1 Int))
                    (=>
                      (and (<= 0 j$1) (< j$1 ($Program.ArrayMax.M.len a^36)))
                      ($IntHeapChunkCompare
                        ($FracChunkConstr (select m^2 j$1) 1)
                        (select $Program.ArrayMax.value@OwnHeap$2
                          ($Program.ArrayMax.M.loc a^36 j$1))))))))
(check-sat)
(pop 1)
(assert
        (forall ((j$1 Int))
                (=> (and (<= 0 j$1) (< j$1 ($Program.ArrayMax.M.len a^36)))
                  (=
                    (select $Program.ArrayMax.value@OwnHeap$3
                      ($Program.ArrayMax.M.loc a^36 j$1))
                    ($IntFracChunkSubtract
                      (select $Program.ArrayMax.value@OwnHeap$2
                        ($Program.ArrayMax.M.loc a^36 j$1))
                      ($FracChunkConstr (select m^2 j$1) 1))))))
(assert
        (forall ((l $Loc))
                (or
                  (exists ((j$1 Int))
                          (and (= l ($Program.ArrayMax.M.loc a^36 j$1))
                            (and (<= 0 j$1)
                              (< j$1 ($Program.ArrayMax.M.len a^36)))))
                  (= (select $Program.ArrayMax.value@OwnHeap$3 l)
                    (select $Program.ArrayMax.value@OwnHeap$2 l)))))
(declare-const $Program.ArrayMax.arr$Pred$Heap$6
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$6 $index) 0)))
(assert
        (forall ((x0$4 $Program.ArrayMax.M.T) (x1$4 (Array Int Int)))
                (ite (and (= x0$4 a^36) (= x1$4 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$6
                      ($Program.ArrayMax.arr$Pred$Constr x0$4 x1$4))
                    (+ 1
                      (select $Program.ArrayMax.arr$Pred$Heap$5
                        ($Program.ArrayMax.arr$Pred$Constr x0$4 x1$4))))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$6
                      ($Program.ArrayMax.arr$Pred$Constr x0$4 x1$4))
                    (select $Program.ArrayMax.arr$Pred$Heap$5
                      ($Program.ArrayMax.arr$Pred$Constr x0$4 x1$4))))))
(declare-const $Program.ArrayMax.arr$Pred$Heap$7
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$7 $index) 0)))
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (<= 1
              (select $Program.ArrayMax.arr$Pred$Heap$6
                ($Program.ArrayMax.arr$Pred$Constr a^36 m^2))))))
(check-sat)
(pop 1)
(assert
        (forall ((x0$5 $Program.ArrayMax.M.T) (x1$5 (Array Int Int)))
                (ite (and (= x0$5 a^36) (= x1$5 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$7
                      ($Program.ArrayMax.arr$Pred$Constr x0$5 x1$5))
                    (-
                      (select $Program.ArrayMax.arr$Pred$Heap$6
                        ($Program.ArrayMax.arr$Pred$Constr x0$5 x1$5))
                      1))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$7
                      ($Program.ArrayMax.arr$Pred$Constr x0$5 x1$5))
                    (select $Program.ArrayMax.arr$Pred$Heap$6
                      ($Program.ArrayMax.arr$Pred$Constr x0$5 x1$5))))))
(push 1)
(assert (not (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (<= 0 x$5))))
(check-sat)
(pop 1)
(push 1)
(assert (not (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (<= x$5 y$4))))
(check-sat)
(pop 1)
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (< y$4 ($Program.ArrayMax.M.len a^36)))))
(check-sat)
(pop 1)
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (forall ((i$4 Int))
                    (or
                      (=>
                        (or (and (<= 0 i$4) (< i$4 x$5))
                          (and (< y$4 i$4)
                            (< i$4 ($Program.ArrayMax.M.len a^36))))
                        (< (select m^2 i$4) (select m^2 x$5)))
                      (=>
                        (or (and (<= 0 i$4) (< i$4 x$5))
                          (and (< y$4 i$4)
                            (< i$4 ($Program.ArrayMax.M.len a^36))))
                        (<= (select m^2 i$4) (select m^2 y$4))))))))
(check-sat)
(pop 1)
(pop 1)
; Inhaling invariants with havoc-ed variables

(declare-const $Program.ArrayMax.arr$Pred$Heap$8
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$8 $index) 0)))
(assert
        (forall ((x0$6 $Program.ArrayMax.M.T) (x1$6 (Array Int Int)))
                (ite (and (= x0$6 a^36) (= x1$6 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$8
                      ($Program.ArrayMax.arr$Pred$Constr x0$6 x1$6))
                    (+ 1
                      (select $Program.ArrayMax.arr$Pred$Heap$2
                        ($Program.ArrayMax.arr$Pred$Constr x0$6 x1$6))))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$8
                      ($Program.ArrayMax.arr$Pred$Constr x0$6 x1$6))
                    (select $Program.ArrayMax.arr$Pred$Heap$2
                      ($Program.ArrayMax.arr$Pred$Constr x0$6 x1$6))))))
(assert (<= 0 x$3))
(assert (<= x$3 y$2))
(assert (< y$2 ($Program.ArrayMax.M.len a^36)))
(assert
        (forall ((i$5 Int))
                (or
                  (=>
                    (or (and (<= 0 i$5) (< i$5 x$3))
                      (and (< y$2 i$5)
                        (< i$5 ($Program.ArrayMax.M.len a^36))))
                    (< (select m^2 i$5) (select m^2 x$3)))
                  (=>
                    (or (and (<= 0 i$5) (< i$5 x$3))
                      (and (< y$2 i$5)
                        (< i$5 ($Program.ArrayMax.M.len a^36))))
                    (<= (select m^2 i$5) (select m^2 y$2))))))
(assert (not (not (= x$3 y$2))))
; Unifying conditional branches

(declare-const x$6 Int)
(declare-const $Program.ArrayMax.arr$Pred$Heap$9
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$9 $index) 0)))
(assert (=> (= ($Program.ArrayMax.M.len a^36) 0) (= x$1 x$6)))
(assert (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (= x$3 x$6)))
(assert
        (=> (= ($Program.ArrayMax.M.len a^36) 0)
          (= $Program.ArrayMax.arr$Pred$Heap$1
            $Program.ArrayMax.arr$Pred$Heap$9)))
(assert
        (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
          (= $Program.ArrayMax.arr$Pred$Heap$8
            $Program.ArrayMax.arr$Pred$Heap$9)))
; Finished unifying conditional branches

; Exhaling body of predicate
(push 1)
(assert
        (not
          (forall ((j$2 Int))
                  (=> (and (<= 0 j$2) (< j$2 ($Program.ArrayMax.M.len a^36)))
                    (<= (select m^2 j$2) (select m^2 x$6))))))
(check-sat)
(pop 1)
(declare-const $Program.ArrayMax.is_max$Pred$Heap$2
             ($PredHeap $Program.ArrayMax.is_max$Pred))
(assert
        (forall (($index $Program.ArrayMax.is_max$Pred))
                (>= (select $Program.ArrayMax.is_max$Pred$Heap$2 $index) 0)))
(assert
        (forall ((x0$7 Int) (x1$7 (Array Int Int)) (x2 Int))
                (ite
                  (and (= x0$7 x$6) (= x1$7 m^2)
                    (= x2 ($Program.ArrayMax.M.len a^36)))
                  (=
                    (select $Program.ArrayMax.is_max$Pred$Heap$2
                      ($Program.ArrayMax.is_max$Pred$Constr x0$7 x1$7 x2))
                    (+ 1
                      (select $Program.ArrayMax.is_max$Pred$Heap
                        ($Program.ArrayMax.is_max$Pred$Constr x0$7 x1$7 x2))))
                  (=
                    (select $Program.ArrayMax.is_max$Pred$Heap$2
                      ($Program.ArrayMax.is_max$Pred$Constr x0$7 x1$7 x2))
                    (select $Program.ArrayMax.is_max$Pred$Heap
                      ($Program.ArrayMax.is_max$Pred$Constr x0$7 x1$7 x2))))))
; Exhaling post-conditions
(declare-const $Program.ArrayMax.arr$Pred$Heap$10
             ($PredHeap $Program.ArrayMax.arr$Pred))
(assert
        (forall (($index $Program.ArrayMax.arr$Pred))
                (>= (select $Program.ArrayMax.arr$Pred$Heap$10 $index) 0)))
(push 1)
(assert
        (not
          (<= 1
            (select $Program.ArrayMax.arr$Pred$Heap$9
              ($Program.ArrayMax.arr$Pred$Constr a^36 m^2)))))
(check-sat)
(pop 1)
(assert
        (forall ((x0$8 $Program.ArrayMax.M.T) (x1$8 (Array Int Int)))
                (ite (and (= x0$8 a^36) (= x1$8 m^2))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$10
                      ($Program.ArrayMax.arr$Pred$Constr x0$8 x1$8))
                    (-
                      (select $Program.ArrayMax.arr$Pred$Heap$9
                        ($Program.ArrayMax.arr$Pred$Constr x0$8 x1$8))
                      1))
                  (=
                    (select $Program.ArrayMax.arr$Pred$Heap$10
                      ($Program.ArrayMax.arr$Pred$Constr x0$8 x1$8))
                    (select $Program.ArrayMax.arr$Pred$Heap$9
                      ($Program.ArrayMax.arr$Pred$Constr x0$8 x1$8))))))
(push 1)
(assert (not (=> (= ($Program.ArrayMax.M.len a^36) 0) (= x$6 (* -1 1)))))
(check-sat)
(pop 1)
(push 1)
(assert (not (=> (not (= ($Program.ArrayMax.M.len a^36) 0)) (<= 0 x$6))))
(check-sat)
(pop 1)
(push 1)
(assert
        (not
          (=> (not (= ($Program.ArrayMax.M.len a^36) 0))
            (< x$6 ($Program.ArrayMax.M.len a^36)))))
(check-sat)
(pop 1)
(assert (ite (= ($Program.ArrayMax.M.len a^36) 0) true true))
(declare-const $Program.ArrayMax.is_max$Pred$Heap$3
             ($PredHeap $Program.ArrayMax.is_max$Pred))
(assert
        (forall (($index $Program.ArrayMax.is_max$Pred))
                (>= (select $Program.ArrayMax.is_max$Pred$Heap$3 $index) 0)))
(push 1)
(assert
        (not
          (<= 1
            (select $Program.ArrayMax.is_max$Pred$Heap$2
              ($Program.ArrayMax.is_max$Pred$Constr x$6 m^2
                ($Program.ArrayMax.M.len a^36))))))
(check-sat)
(pop 1)
(assert
        (forall ((x0$9 Int) (x1$9 (Array Int Int)) (x2$1 Int))
                (ite
                  (and (= x0$9 x$6) (= x1$9 m^2)
                    (= x2$1 ($Program.ArrayMax.M.len a^36)))
                  (=
                    (select $Program.ArrayMax.is_max$Pred$Heap$3
                      ($Program.ArrayMax.is_max$Pred$Constr x0$9 x1$9 x2$1))
                    (-
                      (select $Program.ArrayMax.is_max$Pred$Heap$2
                        ($Program.ArrayMax.is_max$Pred$Constr x0$9 x1$9 x2$1))
                      1))
                  (=
                    (select $Program.ArrayMax.is_max$Pred$Heap$3
                      ($Program.ArrayMax.is_max$Pred$Constr x0$9 x1$9 x2$1))
                    (select $Program.ArrayMax.is_max$Pred$Heap$2
                      ($Program.ArrayMax.is_max$Pred$Constr x0$9 x1$9 x2$1))))))
(pop 1)

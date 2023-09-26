(get-info :version)
; (:version "4.8.7")
; Started: 2023-09-21 11:45:33
; Silicon.version: 1.1-SNAPSHOT (7f2e6823@(detached))
; Input file: <unknown>
; Verifier id: 00
; ------------------------------------------------------------
; Begin preamble
; ////////// Static preamble
; 
; ; /z3config.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :type_check true)
(set-option :smt.bv.reflect true)
(set-option :smt.mbqi false)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :smt.qi.max_multi_patterns 1000)
(set-option :smt.phase_selection 0) ; default: 3, Boogie: 0
(set-option :sat.phase caching)
(set-option :sat.random_seed 0)
(set-option :nlsat.randomize true)
(set-option :nlsat.seed 0)
(set-option :nlsat.shuffle_vars false)
(set-option :fp.spacer.order_children 0) ; Not available with Z3 4.5
(set-option :fp.spacer.random_seed 0) ; Not available with Z3 4.5
(set-option :smt.arith.random_initial_value true) ; Boogie: true
(set-option :smt.random_seed 0)
(set-option :sls.random_offset true)
(set-option :sls.random_seed 0)
(set-option :sls.restart_init false)
(set-option :sls.walksat_ucb true)
(set-option :model.v2 true)
; 
; ; /preamble.smt2
(declare-datatypes (($Snap 0)) ((
    ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)
(declare-sort $FPM 0)
(declare-sort $PPM 0)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
; ////////// Sorts
; ////////// Sort wrappers
; Declaring additional sort wrappers
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    :qid |$Snap.$SnapToIntTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.IntTo$Snap($SortWrappers.$SnapToInt x)))
    :pattern (($SortWrappers.$SnapToInt x))
    :qid |$Snap.IntTo$SnapToInt|
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    :qid |$Snap.$SnapToBoolTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.BoolTo$Snap($SortWrappers.$SnapToBool x)))
    :pattern (($SortWrappers.$SnapToBool x))
    :qid |$Snap.BoolTo$SnapToBool|
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    :qid |$Snap.$SnapTo$RefTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.$RefTo$Snap($SortWrappers.$SnapTo$Ref x)))
    :pattern (($SortWrappers.$SnapTo$Ref x))
    :qid |$Snap.$RefTo$SnapTo$Ref|
    )))
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    :qid |$Snap.$SnapTo$PermTo$Snap|
    )))
(assert (forall ((x $Snap)) (!
    (= x ($SortWrappers.$PermTo$Snap($SortWrappers.$SnapTo$Perm x)))
    :pattern (($SortWrappers.$SnapTo$Perm x))
    :qid |$Snap.$PermTo$SnapTo$Perm|
    )))
; ////////// Symbols
; Declaring symbols related to program functions (from program analysis)
; Snapshot variable to be used during function verification
(declare-fun s@$ () $Snap)
; Declaring predicate trigger functions
; ////////// Uniqueness assumptions from domains
; ////////// Axioms
; End preamble
; ------------------------------------------------------------
; State saturation: after preamble
(set-option :timeout 100)
(check-sat)
; unknown
; ------------------------------------------------------------
; Begin function- and predicate-related preamble
; Declaring symbols related to program functions (from verification)
; End function- and predicate-related preamble
; ------------------------------------------------------------
; ---------- reverse ----------
(set-option :timeout 0)
(push) ; 1
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 0)
(push) ; 2
(pop) ; 2
(push) ; 2
; [exec]
; var curr: Int
(declare-const curr@0@11 Int)
; [exec]
; var curr__next_pre: Int
(declare-const curr__next_pre@1@11 Int)
; [exec]
; var curr__flow_pre: Int
(declare-const curr__flow_pre@2@11 Int)
; [exec]
; var curr__next_post: Int
(declare-const curr__next_post@3@11 Int)
; [exec]
; var curr__flow_post: Int
(declare-const curr__flow_post@4@11 Int)
; [exec]
; var prev: Int
(declare-const prev@5@11 Int)
; [exec]
; var prev__next_pre: Int
(declare-const prev__next_pre@6@11 Int)
; [exec]
; var prev__flow_pre: Int
(declare-const prev__flow_pre@7@11 Int)
; [exec]
; var prev__next_post: Int
(declare-const prev__next_post@8@11 Int)
; [exec]
; var prev__flow_post: Int
(declare-const prev__flow_post@9@11 Int)
; [exec]
; var succ: Int
(declare-const succ@10@11 Int)
; [exec]
; var succ__next_pre: Int
(declare-const succ__next_pre@11@11 Int)
; [exec]
; var succ__flow_pre: Int
(declare-const succ__flow_pre@12@11 Int)
; [exec]
; var succ__next_post: Int
(declare-const succ__next_post@13@11 Int)
; [exec]
; var succ__flow_post: Int
(declare-const succ__flow_post@14@11 Int)
; [exec]
; var AllocationCounter: Int
(declare-const AllocationCounter@15@11 Int)
; [exec]
; var HeadLeftPre: Int
(declare-const HeadLeftPre@16@11 Int)
; [exec]
; var HeadLeftPost: Int
(declare-const HeadLeftPost@17@11 Int)
; [exec]
; var HeadRightPre: Int
(declare-const HeadRightPre@18@11 Int)
; [exec]
; var HeadRightPost: Int
(declare-const HeadRightPost@19@11 Int)
; [exec]
; AllocationCounter := 0
; [exec]
; HeadLeftPre := curr
; [exec]
; HeadLeftPost := curr
; [exec]
; HeadRightPre := -1
; [eval] -1
; [exec]
; HeadRightPost := -1
; [eval] -1
; [exec]
; inhale curr >= -1
(declare-const $t@20@11 $Snap)
(assert (= $t@20@11 $Snap.unit))
; [eval] curr >= -1
; [eval] -1
(assert (>= curr@0@11 (- 0 1)))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; curr__next_pre := nondet()
(declare-const res@21@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; curr__flow_pre := nondet()
(declare-const res@22@11 Int)
; State saturation: after contract
(check-sat)
; unknown
; [exec]
; inhale curr >= -1
(declare-const $t@23@11 $Snap)
(assert (= $t@23@11 $Snap.unit))
; [eval] curr >= -1
; [eval] -1
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr__flow_pre == (curr != -1 ? 1 : 2)
(declare-const $t@24@11 $Snap)
(assert (= $t@24@11 $Snap.unit))
; [eval] curr__flow_pre == (curr != -1 ? 1 : 2)
; [eval] (curr != -1 ? 1 : 2)
; [eval] curr != -1
; [eval] -1
(set-option :timeout 0)
(push) ; 3
(push) ; 4
(set-option :timeout 10)
(assert (not (= curr@0@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 10)
(assert (not (not (= curr@0@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [then-branch: 0 | curr@0@11 != -1 | live]
; [else-branch: 0 | curr@0@11 == -1 | live]
(set-option :timeout 0)
(push) ; 4
; [then-branch: 0 | curr@0@11 != -1]
(assert (not (= curr@0@11 (- 0 1))))
(pop) ; 4
(push) ; 4
; [else-branch: 0 | curr@0@11 == -1]
(assert (= curr@0@11 (- 0 1)))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (= curr@0@11 (- 0 1)) (not (= curr@0@11 (- 0 1)))))
(assert (= res@22@11 (ite (not (= curr@0@11 (- 0 1))) 1 2)))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr == -1 ==> curr__next_pre < -1
(declare-const $t@25@11 $Snap)
(assert (= $t@25@11 $Snap.unit))
; [eval] curr == -1 ==> curr__next_pre < -1
; [eval] curr == -1
; [eval] -1
(set-option :timeout 0)
(push) ; 3
(push) ; 4
(set-option :timeout 10)
(assert (not (not (= curr@0@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 4
(set-option :timeout 10)
(assert (not (= curr@0@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [then-branch: 1 | curr@0@11 == -1 | live]
; [else-branch: 1 | curr@0@11 != -1 | live]
(set-option :timeout 0)
(push) ; 4
; [then-branch: 1 | curr@0@11 == -1]
(assert (= curr@0@11 (- 0 1)))
; [eval] curr__next_pre < -1
; [eval] -1
(pop) ; 4
(push) ; 4
; [else-branch: 1 | curr@0@11 != -1]
(assert (not (= curr@0@11 (- 0 1))))
(pop) ; 4
(pop) ; 3
; Joined path conditions
; Joined path conditions
(assert (or (not (= curr@0@11 (- 0 1))) (= curr@0@11 (- 0 1))))
(assert (=> (= curr@0@11 (- 0 1)) (< res@21@11 (- 0 1))))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale true
(declare-const $t@26@11 $Snap)
(assert (= $t@26@11 $Snap.unit))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; prev := -1
; [eval] -1
; [exec]
; prev__next_pre := nondet()
(declare-const res@27@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; prev__flow_pre := nondet()
(declare-const res@28@11 Int)
; State saturation: after contract
(check-sat)
; unknown
; [exec]
; inhale prev >= -1
(declare-const $t@29@11 $Snap)
(assert (= $t@29@11 $Snap.unit))
; [eval] prev >= -1
; [eval] -1
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale prev__flow_pre == (prev != -1 ? 1 : 2)
(declare-const $t@30@11 $Snap)
(assert (= $t@30@11 $Snap.unit))
; [eval] prev__flow_pre == (prev != -1 ? 1 : 2)
; [eval] (prev != -1 ? 1 : 2)
; [eval] prev != -1
; [eval] -1
(set-option :timeout 0)
(push) ; 3
; [then-branch: 2 | False | dead]
; [else-branch: 2 | True | live]
(push) ; 4
; [else-branch: 2 | True]
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (= res@28@11 2))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale prev == -1 ==> prev__next_pre < -1
(declare-const $t@31@11 $Snap)
(assert (= $t@31@11 $Snap.unit))
; [eval] prev == -1 ==> prev__next_pre < -1
; [eval] prev == -1
; [eval] -1
(set-option :timeout 0)
(push) ; 3
(push) ; 4
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [then-branch: 3 | True | live]
; [else-branch: 3 | False | dead]
(set-option :timeout 0)
(push) ; 4
; [then-branch: 3 | True]
; [eval] prev__next_pre < -1
; [eval] -1
(pop) ; 4
(pop) ; 3
; Joined path conditions
(assert (< res@27@11 (- 0 1)))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale true
(declare-const $t@32@11 $Snap)
(assert (= $t@32@11 $Snap.unit))
; State saturation: after inhale
(check-sat)
; unknown
(declare-const succ@33@11 Int)
(declare-const succ__next_pre@34@11 Int)
(declare-const succ__flow_pre@35@11 Int)
(declare-const succ__next_post@36@11 Int)
(declare-const succ__flow_post@37@11 Int)
(declare-const HeadLeftPre@38@11 Int)
(declare-const HeadRightPre@39@11 Int)
(declare-const HeadRightPost@40@11 Int)
(declare-const HeadLeftPost@41@11 Int)
(declare-const curr__next_post@42@11 Int)
(declare-const curr__flow_post@43@11 Int)
(declare-const prev__next_post@44@11 Int)
(declare-const prev__flow_post@45@11 Int)
(declare-const prev__externalInflow@46@11 Int)
(declare-const prev__globalInflowPre@47@11 Int)
(declare-const prev__globalInflowPost@48@11 Int)
(declare-const curr__externalInflow@49@11 Int)
(declare-const curr__globalInflowPre@50@11 Int)
(declare-const curr__globalInflowPost@51@11 Int)
(declare-const succ__externalInflow@52@11 Int)
(declare-const succ__globalInflowPre@53@11 Int)
(declare-const succ__globalInflowPost@54@11 Int)
(declare-const new_prev_flow_pre@55@11 Int)
(declare-const new_curr_flow_pre@56@11 Int)
(declare-const new_succ_flow_pre@57@11 Int)
(declare-const fixpoint1@58@11 Bool)
(declare-const new_prev_flow_pre2@59@11 Int)
(declare-const new_curr_flow_pre2@60@11 Int)
(declare-const new_succ_flow_pre2@61@11 Int)
(declare-const new_prev_flow_post@62@11 Int)
(declare-const new_curr_flow_post@63@11 Int)
(declare-const new_succ_flow_post@64@11 Int)
(declare-const fixpoint2@65@11 Bool)
(declare-const new_prev_flow_post2@66@11 Int)
(declare-const new_curr_flow_post2@67@11 Int)
(declare-const new_succ_flow_post2@68@11 Int)
(declare-const prev@69@11 Int)
(declare-const prev__next_pre@70@11 Int)
(declare-const prev__flow_pre@71@11 Int)
(declare-const curr@72@11 Int)
(declare-const curr__next_pre@73@11 Int)
(declare-const curr__flow_pre@74@11 Int)
(set-option :timeout 0)
(push) ; 3
; Loop head block: Check well-definedness of invariant
(declare-const $t@75@11 $Snap)
(assert (= $t@75@11 ($Snap.combine ($Snap.first $t@75@11) ($Snap.second $t@75@11))))
(assert (= ($Snap.first $t@75@11) $Snap.unit))
; [eval] curr >= -1
; [eval] -1
(assert (>= curr@72@11 (- 0 1)))
(assert (=
  ($Snap.second $t@75@11)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@75@11))
    ($Snap.second ($Snap.second $t@75@11)))))
(assert (= ($Snap.first ($Snap.second $t@75@11)) $Snap.unit))
; [eval] curr__flow_pre == (curr != -1 ? 1 : 2)
; [eval] (curr != -1 ? 1 : 2)
; [eval] curr != -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@72@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 4 | curr@72@11 != -1 | live]
; [else-branch: 4 | curr@72@11 == -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 4 | curr@72@11 != -1]
(assert (not (= curr@72@11 (- 0 1))))
(pop) ; 5
(push) ; 5
; [else-branch: 4 | curr@72@11 == -1]
(assert (= curr@72@11 (- 0 1)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (= curr@72@11 (- 0 1)) (not (= curr@72@11 (- 0 1)))))
(assert (= curr__flow_pre@74@11 (ite (not (= curr@72@11 (- 0 1))) 1 2)))
(assert (=
  ($Snap.second ($Snap.second $t@75@11))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@75@11)))
    ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@75@11))) $Snap.unit))
; [eval] curr == -1 ==> curr__next_pre < -1
; [eval] curr == -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@72@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 5 | curr@72@11 == -1 | live]
; [else-branch: 5 | curr@72@11 != -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 5 | curr@72@11 == -1]
(assert (= curr@72@11 (- 0 1)))
; [eval] curr__next_pre < -1
; [eval] -1
(pop) ; 5
(push) ; 5
; [else-branch: 5 | curr@72@11 != -1]
(assert (not (= curr@72@11 (- 0 1))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (= curr@72@11 (- 0 1))) (= curr@72@11 (- 0 1))))
(assert (=> (= curr@72@11 (- 0 1)) (< curr__next_pre@73@11 (- 0 1))))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@75@11)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
  $Snap.unit))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
  $Snap.unit))
; [eval] prev >= -1
; [eval] -1
(assert (>= prev@69@11 (- 0 1)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
  $Snap.unit))
; [eval] prev__flow_pre == (prev != -1 ? 1 : 2)
; [eval] (prev != -1 ? 1 : 2)
; [eval] prev != -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (= prev@69@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= prev@69@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 6 | prev@69@11 != -1 | live]
; [else-branch: 6 | prev@69@11 == -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 6 | prev@69@11 != -1]
(assert (not (= prev@69@11 (- 0 1))))
(pop) ; 5
(push) ; 5
; [else-branch: 6 | prev@69@11 == -1]
(assert (= prev@69@11 (- 0 1)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (= prev@69@11 (- 0 1)) (not (= prev@69@11 (- 0 1)))))
(assert (= prev__flow_pre@71@11 (ite (not (= prev@69@11 (- 0 1))) 1 2)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
  $Snap.unit))
; [eval] prev == -1 ==> prev__next_pre < -1
; [eval] prev == -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= prev@69@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (= prev@69@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 7 | prev@69@11 == -1 | live]
; [else-branch: 7 | prev@69@11 != -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 7 | prev@69@11 == -1]
(assert (= prev@69@11 (- 0 1)))
; [eval] prev__next_pre < -1
; [eval] -1
(pop) ; 5
(push) ; 5
; [else-branch: 7 | prev@69@11 != -1]
(assert (not (= prev@69@11 (- 0 1))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
(assert (or (not (= prev@69@11 (- 0 1))) (= prev@69@11 (- 0 1))))
(assert (=> (= prev@69@11 (- 0 1)) (< prev__next_pre@70@11 (- 0 1))))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
  $Snap.unit))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
  $Snap.unit))
; [eval] HeadLeftPost == curr
(assert (= HeadLeftPost@41@11 curr@72@11))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
  $Snap.unit))
; [eval] HeadRightPost == prev
(assert (= HeadRightPost@40@11 prev@69@11))
; Loop head block: Check well-definedness of edge conditions
(push) ; 4
; [eval] curr != -1
; [eval] -1
(pop) ; 4
(push) ; 4
; [eval] !(curr != -1)
; [eval] curr != -1
; [eval] -1
(pop) ; 4
(pop) ; 3
(push) ; 3
; Loop head block: Establish invariant
; [eval] curr >= -1
; [eval] -1
; [eval] curr__flow_pre == (curr != -1 ? 1 : 2)
; [eval] (curr != -1 ? 1 : 2)
; [eval] curr != -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@0@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@0@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 8 | curr@0@11 != -1 | live]
; [else-branch: 8 | curr@0@11 == -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 8 | curr@0@11 != -1]
(assert (not (= curr@0@11 (- 0 1))))
(pop) ; 5
(push) ; 5
; [else-branch: 8 | curr@0@11 == -1]
(assert (= curr@0@11 (- 0 1)))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
; [eval] curr == -1 ==> curr__next_pre < -1
; [eval] curr == -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@0@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@0@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 9 | curr@0@11 == -1 | live]
; [else-branch: 9 | curr@0@11 != -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 9 | curr@0@11 == -1]
(assert (= curr@0@11 (- 0 1)))
; [eval] curr__next_pre < -1
; [eval] -1
(pop) ; 5
(push) ; 5
; [else-branch: 9 | curr@0@11 != -1]
(assert (not (= curr@0@11 (- 0 1))))
(pop) ; 5
(pop) ; 4
; Joined path conditions
; Joined path conditions
; [eval] prev >= -1
; [eval] -1
; [eval] prev__flow_pre == (prev != -1 ? 1 : 2)
; [eval] (prev != -1 ? 1 : 2)
; [eval] prev != -1
; [eval] -1
(push) ; 4
; [then-branch: 10 | False | dead]
; [else-branch: 10 | True | live]
(push) ; 5
; [else-branch: 10 | True]
(pop) ; 5
(pop) ; 4
; Joined path conditions
; [eval] prev == -1 ==> prev__next_pre < -1
; [eval] prev == -1
; [eval] -1
(push) ; 4
(push) ; 5
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 11 | True | live]
; [else-branch: 11 | False | dead]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 11 | True]
; [eval] prev__next_pre < -1
; [eval] -1
(pop) ; 5
(pop) ; 4
; Joined path conditions
; [eval] HeadLeftPost == curr
; [eval] HeadRightPost == prev
; Loop head block: Execute statements of loop head block (in invariant state)
(push) ; 4
(assert (= $t@75@11 ($Snap.combine ($Snap.first $t@75@11) ($Snap.second $t@75@11))))
(assert (= ($Snap.first $t@75@11) $Snap.unit))
(assert (>= curr@72@11 (- 0 1)))
(assert (=
  ($Snap.second $t@75@11)
  ($Snap.combine
    ($Snap.first ($Snap.second $t@75@11))
    ($Snap.second ($Snap.second $t@75@11)))))
(assert (= ($Snap.first ($Snap.second $t@75@11)) $Snap.unit))
(assert (or (= curr@72@11 (- 0 1)) (not (= curr@72@11 (- 0 1)))))
(assert (= curr__flow_pre@74@11 (ite (not (= curr@72@11 (- 0 1))) 1 2)))
(assert (=
  ($Snap.second ($Snap.second $t@75@11))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second $t@75@11)))
    ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
(assert (= ($Snap.first ($Snap.second ($Snap.second $t@75@11))) $Snap.unit))
(assert (or (not (= curr@72@11 (- 0 1))) (= curr@72@11 (- 0 1))))
(assert (=> (= curr@72@11 (- 0 1)) (< curr__next_pre@73@11 (- 0 1))))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second $t@75@11)))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
  $Snap.unit))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
  $Snap.unit))
(assert (>= prev@69@11 (- 0 1)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
  $Snap.unit))
(assert (or (= prev@69@11 (- 0 1)) (not (= prev@69@11 (- 0 1)))))
(assert (= prev__flow_pre@71@11 (ite (not (= prev@69@11 (- 0 1))) 1 2)))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
  $Snap.unit))
(assert (or (not (= prev@69@11 (- 0 1))) (= prev@69@11 (- 0 1))))
(assert (=> (= prev@69@11 (- 0 1)) (< prev__next_pre@70@11 (- 0 1))))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
  $Snap.unit))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))
  ($Snap.combine
    ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
    ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11))))))))))))
(assert (=
  ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
  $Snap.unit))
(assert (= HeadLeftPost@41@11 curr@72@11))
(assert (=
  ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second $t@75@11)))))))))
  $Snap.unit))
(assert (= HeadRightPost@40@11 prev@69@11))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 10)
(check-sat)
; unknown
; Loop head block: Follow loop-internal edges
; [eval] curr != -1
; [eval] -1
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@72@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 12 | curr@72@11 != -1 | live]
; [else-branch: 12 | curr@72@11 == -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 12 | curr@72@11 != -1]
(assert (not (= curr@72@11 (- 0 1))))
; [exec]
; var prev__externalInflow: Int
(declare-const prev__externalInflow@76@11 Int)
; [exec]
; var prev__globalInflowPre: Int
(declare-const prev__globalInflowPre@77@11 Int)
; [exec]
; var prev__globalInflowPost: Int
(declare-const prev__globalInflowPost@78@11 Int)
; [exec]
; var curr__externalInflow: Int
(declare-const curr__externalInflow@79@11 Int)
; [exec]
; var curr__globalInflowPre: Int
(declare-const curr__globalInflowPre@80@11 Int)
; [exec]
; var curr__globalInflowPost: Int
(declare-const curr__globalInflowPost@81@11 Int)
; [exec]
; var succ__externalInflow: Int
(declare-const succ__externalInflow@82@11 Int)
; [exec]
; var succ__globalInflowPre: Int
(declare-const succ__globalInflowPre@83@11 Int)
; [exec]
; var succ__globalInflowPost: Int
(declare-const succ__globalInflowPost@84@11 Int)
; [exec]
; var new_prev_flow_pre: Int
(declare-const new_prev_flow_pre@85@11 Int)
; [exec]
; var new_curr_flow_pre: Int
(declare-const new_curr_flow_pre@86@11 Int)
; [exec]
; var new_succ_flow_pre: Int
(declare-const new_succ_flow_pre@87@11 Int)
; [exec]
; var fixpoint1: Bool
(declare-const fixpoint1@88@11 Bool)
; [exec]
; var new_prev_flow_post: Int
(declare-const new_prev_flow_post@89@11 Int)
; [exec]
; var new_curr_flow_post: Int
(declare-const new_curr_flow_post@90@11 Int)
; [exec]
; var new_succ_flow_post: Int
(declare-const new_succ_flow_post@91@11 Int)
; [exec]
; var fixpoint2: Bool
(declare-const fixpoint2@92@11 Bool)
; [exec]
; var node: Int
(declare-const node@93@11 Int)
; [exec]
; succ := curr__next_pre
; [exec]
; succ__next_pre := nondet()
(declare-const res@94@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; succ__flow_pre := nondet()
(declare-const res@95@11 Int)
; State saturation: after contract
(check-sat)
; unknown
; [exec]
; inhale succ__flow_pre >= (curr__flow_pre >= 3 ? 3 : curr__flow_pre)
(declare-const $t@96@11 $Snap)
(assert (= $t@96@11 $Snap.unit))
; [eval] succ__flow_pre >= (curr__flow_pre >= 3 ? 3 : curr__flow_pre)
; [eval] (curr__flow_pre >= 3 ? 3 : curr__flow_pre)
; [eval] curr__flow_pre >= 3
(set-option :timeout 0)
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (>= curr__flow_pre@74@11 3))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 13 | curr__flow_pre@74@11 >= 3 | dead]
; [else-branch: 13 | !(curr__flow_pre@74@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 7
; [else-branch: 13 | !(curr__flow_pre@74@11 >= 3)]
(assert (not (>= curr__flow_pre@74@11 3)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
(assert (not (>= curr__flow_pre@74@11 3)))
(assert (>= res@95@11 curr__flow_pre@74@11))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale succ >= -1
(declare-const $t@97@11 $Snap)
(assert (= $t@97@11 $Snap.unit))
; [eval] succ >= -1
; [eval] -1
(assert (>= curr__next_pre@73@11 (- 0 1)))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale succ__flow_pre == (succ != -1 ? 1 : 2)
(declare-const $t@98@11 $Snap)
(assert (= $t@98@11 $Snap.unit))
; [eval] succ__flow_pre == (succ != -1 ? 1 : 2)
; [eval] (succ != -1 ? 1 : 2)
; [eval] succ != -1
; [eval] -1
(set-option :timeout 0)
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 14 | curr__next_pre@73@11 != -1 | live]
; [else-branch: 14 | curr__next_pre@73@11 == -1 | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 14 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 7
(push) ; 7
; [else-branch: 14 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (= curr__next_pre@73@11 (- 0 1)) (not (= curr__next_pre@73@11 (- 0 1)))))
(assert (= res@95@11 (ite (not (= curr__next_pre@73@11 (- 0 1))) 1 2)))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale succ == -1 ==> succ__next_pre < -1
(declare-const $t@99@11 $Snap)
(assert (= $t@99@11 $Snap.unit))
; [eval] succ == -1 ==> succ__next_pre < -1
; [eval] succ == -1
; [eval] -1
(set-option :timeout 0)
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 15 | curr__next_pre@73@11 == -1 | live]
; [else-branch: 15 | curr__next_pre@73@11 != -1 | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 15 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
; [eval] succ__next_pre < -1
; [eval] -1
(pop) ; 7
(push) ; 7
; [else-branch: 15 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (not (= curr__next_pre@73@11 (- 0 1))) (= curr__next_pre@73@11 (- 0 1))))
(assert (=> (= curr__next_pre@73@11 (- 0 1)) (< res@94@11 (- 0 1))))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale true
(declare-const $t@100@11 $Snap)
(assert (= $t@100@11 $Snap.unit))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; succ__next_post := succ__next_pre
; [exec]
; succ__flow_post := nondet()
(declare-const res@101@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; HeadLeftPre := HeadLeftPost
; [exec]
; HeadRightPre := HeadRightPost
; [exec]
; HeadRightPost := curr
; [exec]
; HeadLeftPost := succ
; [exec]
; curr__next_post := prev
; [exec]
; curr__flow_post := nondet()
(declare-const res@102@11 Int)
; State saturation: after contract
(check-sat)
; unknown
; [exec]
; prev__next_post := prev__next_pre
; [exec]
; prev__flow_post := nondet()
(declare-const res@103@11 Int)
; State saturation: after contract
(check-sat)
; unknown
; [exec]
; inhale prev__flow_post >= (curr__flow_post >= 3 ? 3 : curr__flow_post)
(declare-const $t@104@11 $Snap)
(assert (= $t@104@11 $Snap.unit))
; [eval] prev__flow_post >= (curr__flow_post >= 3 ? 3 : curr__flow_post)
; [eval] (curr__flow_post >= 3 ? 3 : curr__flow_post)
; [eval] curr__flow_post >= 3
(set-option :timeout 0)
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (>= res@102@11 3))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (>= res@102@11 3)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 16 | res@102@11 >= 3 | live]
; [else-branch: 16 | !(res@102@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 16 | res@102@11 >= 3]
(assert (>= res@102@11 3))
(pop) ; 7
(push) ; 7
; [else-branch: 16 | !(res@102@11 >= 3)]
(assert (not (>= res@102@11 3)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (not (>= res@102@11 3)) (>= res@102@11 3)))
(assert (>= res@103@11 (ite (>= res@102@11 3) 3 res@102@11)))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; prev__externalInflow := nondet()
(declare-const res@105@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; inhale prev__externalInflow >= 0
(declare-const $t@106@11 $Snap)
(assert (= $t@106@11 $Snap.unit))
; [eval] prev__externalInflow >= 0
(assert (>= res@105@11 0))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; prev__globalInflowPre := (prev == HeadLeftPre && prev == HeadRightPre ?
;     2 :
;     (prev == HeadLeftPre || prev == HeadRightPre ? 1 : 0))
; [eval] (prev == HeadLeftPre && prev == HeadRightPre ? 2 : (prev == HeadLeftPre || prev == HeadRightPre ? 1 : 0))
; [eval] prev == HeadLeftPre && prev == HeadRightPre
; [eval] prev == HeadLeftPre
(set-option :timeout 0)
(push) ; 6
; [then-branch: 17 | prev@69@11 == HeadLeftPost@41@11 | live]
; [else-branch: 17 | prev@69@11 != HeadLeftPost@41@11 | live]
(push) ; 7
; [then-branch: 17 | prev@69@11 == HeadLeftPost@41@11]
(assert (= prev@69@11 HeadLeftPost@41@11))
; [eval] prev == HeadRightPre
(pop) ; 7
(push) ; 7
; [else-branch: 17 | prev@69@11 != HeadLeftPost@41@11]
(assert (not (= prev@69@11 HeadLeftPost@41@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (not (= prev@69@11 HeadLeftPost@41@11)) (= prev@69@11 HeadLeftPost@41@11)))
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 18 | prev@69@11 == HeadRightPost@40@11 && prev@69@11 == HeadLeftPost@41@11 | live]
; [else-branch: 18 | !(prev@69@11 == HeadRightPost@40@11 && prev@69@11 == HeadLeftPost@41@11) | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 18 | prev@69@11 == HeadRightPost@40@11 && prev@69@11 == HeadLeftPost@41@11]
(assert (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11)))
(pop) ; 7
(push) ; 7
; [else-branch: 18 | !(prev@69@11 == HeadRightPost@40@11 && prev@69@11 == HeadLeftPost@41@11)]
(assert (not (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11))))
; [eval] (prev == HeadLeftPre || prev == HeadRightPre ? 1 : 0)
; [eval] prev == HeadLeftPre || prev == HeadRightPre
; [eval] prev == HeadLeftPre
(push) ; 8
; [then-branch: 19 | prev@69@11 == HeadLeftPost@41@11 | live]
; [else-branch: 19 | prev@69@11 != HeadLeftPost@41@11 | live]
(push) ; 9
; [then-branch: 19 | prev@69@11 == HeadLeftPost@41@11]
(assert (= prev@69@11 HeadLeftPost@41@11))
(pop) ; 9
(push) ; 9
; [else-branch: 19 | prev@69@11 != HeadLeftPost@41@11]
(assert (not (= prev@69@11 HeadLeftPost@41@11)))
; [eval] prev == HeadRightPre
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not (not (or (= prev@69@11 HeadLeftPost@41@11) (= prev@69@11 HeadRightPost@40@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (or (= prev@69@11 HeadLeftPost@41@11) (= prev@69@11 HeadRightPost@40@11))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 20 | prev@69@11 == HeadLeftPost@41@11 || prev@69@11 == HeadRightPost@40@11 | live]
; [else-branch: 20 | !(prev@69@11 == HeadLeftPost@41@11 || prev@69@11 == HeadRightPost@40@11) | dead]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 20 | prev@69@11 == HeadLeftPost@41@11 || prev@69@11 == HeadRightPost@40@11]
(assert (or (= prev@69@11 HeadLeftPost@41@11) (= prev@69@11 HeadRightPost@40@11)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (or (= prev@69@11 HeadLeftPost@41@11) (= prev@69@11 HeadRightPost@40@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (=>
  (not
    (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11)))
  (and
    (not
      (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11)))
    (or (= prev@69@11 HeadLeftPost@41@11) (= prev@69@11 HeadRightPost@40@11)))))
(assert (or
  (not
    (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11)))
  (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11))))
(declare-const prev__globalInflowPre@107@11 Int)
(assert (=
  prev__globalInflowPre@107@11
  (ite
    (and (= prev@69@11 HeadRightPost@40@11) (= prev@69@11 HeadLeftPost@41@11))
    2
    1)))
; [exec]
; prev__globalInflowPost := (prev == HeadLeftPost && prev == HeadRightPost ?
;     2 :
;     (prev == HeadLeftPost || prev == HeadRightPost ? 1 : 0))
; [eval] (prev == HeadLeftPost && prev == HeadRightPost ? 2 : (prev == HeadLeftPost || prev == HeadRightPost ? 1 : 0))
; [eval] prev == HeadLeftPost && prev == HeadRightPost
; [eval] prev == HeadLeftPost
(push) ; 6
; [then-branch: 21 | prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 21 | prev@69@11 != curr__next_pre@73@11 | live]
(push) ; 7
; [then-branch: 21 | prev@69@11 == curr__next_pre@73@11]
(assert (= prev@69@11 curr__next_pre@73@11))
; [eval] prev == HeadRightPost
(pop) ; 7
(push) ; 7
; [else-branch: 21 | prev@69@11 != curr__next_pre@73@11]
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= prev@69@11 curr__next_pre@73@11))
  (= prev@69@11 curr__next_pre@73@11)))
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 22 | prev@69@11 == curr@72@11 && prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 22 | !(prev@69@11 == curr@72@11 && prev@69@11 == curr__next_pre@73@11) | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 22 | prev@69@11 == curr@72@11 && prev@69@11 == curr__next_pre@73@11]
(assert (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11)))
(pop) ; 7
(push) ; 7
; [else-branch: 22 | !(prev@69@11 == curr@72@11 && prev@69@11 == curr__next_pre@73@11)]
(assert (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11))))
; [eval] (prev == HeadLeftPost || prev == HeadRightPost ? 1 : 0)
; [eval] prev == HeadLeftPost || prev == HeadRightPost
; [eval] prev == HeadLeftPost
(push) ; 8
; [then-branch: 23 | prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 23 | prev@69@11 != curr__next_pre@73@11 | live]
(push) ; 9
; [then-branch: 23 | prev@69@11 == curr__next_pre@73@11]
(assert (= prev@69@11 curr__next_pre@73@11))
(pop) ; 9
(push) ; 9
; [else-branch: 23 | prev@69@11 != curr__next_pre@73@11]
(assert (not (= prev@69@11 curr__next_pre@73@11)))
; [eval] prev == HeadRightPost
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not (not (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 24 | prev@69@11 == curr__next_pre@73@11 || prev@69@11 == curr@72@11 | live]
; [else-branch: 24 | !(prev@69@11 == curr__next_pre@73@11 || prev@69@11 == curr@72@11) | live]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 24 | prev@69@11 == curr__next_pre@73@11 || prev@69@11 == curr@72@11]
(assert (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11)))
(pop) ; 9
(push) ; 9
; [else-branch: 24 | !(prev@69@11 == curr__next_pre@73@11 || prev@69@11 == curr@72@11)]
(assert (not (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11)))
  (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11))))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (=>
  (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11)))
  (and
    (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11)))
    (or
      (not (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11)))
      (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11))))))
(assert (or
  (not (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11)))
  (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11))))
(declare-const prev__globalInflowPost@108@11 Int)
(assert (=
  prev__globalInflowPost@108@11
  (ite
    (and (= prev@69@11 curr@72@11) (= prev@69@11 curr__next_pre@73@11))
    2
    (ite (or (= prev@69@11 curr__next_pre@73@11) (= prev@69@11 curr@72@11)) 1 0))))
; [exec]
; curr__externalInflow := nondet()
(declare-const res@109@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; inhale curr__externalInflow >= 0
(declare-const $t@110@11 $Snap)
(assert (= $t@110@11 $Snap.unit))
; [eval] curr__externalInflow >= 0
(assert (>= res@109@11 0))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; curr__globalInflowPre := (curr == HeadLeftPre && curr == HeadRightPre ?
;     2 :
;     (curr == HeadLeftPre || curr == HeadRightPre ? 1 : 0))
; [eval] (curr == HeadLeftPre && curr == HeadRightPre ? 2 : (curr == HeadLeftPre || curr == HeadRightPre ? 1 : 0))
; [eval] curr == HeadLeftPre && curr == HeadRightPre
; [eval] curr == HeadLeftPre
(set-option :timeout 0)
(push) ; 6
; [then-branch: 25 | curr@72@11 == HeadLeftPost@41@11 | live]
; [else-branch: 25 | curr@72@11 != HeadLeftPost@41@11 | live]
(push) ; 7
; [then-branch: 25 | curr@72@11 == HeadLeftPost@41@11]
(assert (= curr@72@11 HeadLeftPost@41@11))
; [eval] curr == HeadRightPre
(pop) ; 7
(push) ; 7
; [else-branch: 25 | curr@72@11 != HeadLeftPost@41@11]
(assert (not (= curr@72@11 HeadLeftPost@41@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or (not (= curr@72@11 HeadLeftPost@41@11)) (= curr@72@11 HeadLeftPost@41@11)))
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 26 | curr@72@11 == HeadRightPost@40@11 && curr@72@11 == HeadLeftPost@41@11 | live]
; [else-branch: 26 | !(curr@72@11 == HeadRightPost@40@11 && curr@72@11 == HeadLeftPost@41@11) | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 26 | curr@72@11 == HeadRightPost@40@11 && curr@72@11 == HeadLeftPost@41@11]
(assert (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11)))
(pop) ; 7
(push) ; 7
; [else-branch: 26 | !(curr@72@11 == HeadRightPost@40@11 && curr@72@11 == HeadLeftPost@41@11)]
(assert (not (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11))))
; [eval] (curr == HeadLeftPre || curr == HeadRightPre ? 1 : 0)
; [eval] curr == HeadLeftPre || curr == HeadRightPre
; [eval] curr == HeadLeftPre
(push) ; 8
; [then-branch: 27 | curr@72@11 == HeadLeftPost@41@11 | live]
; [else-branch: 27 | curr@72@11 != HeadLeftPost@41@11 | live]
(push) ; 9
; [then-branch: 27 | curr@72@11 == HeadLeftPost@41@11]
(assert (= curr@72@11 HeadLeftPost@41@11))
(pop) ; 9
(push) ; 9
; [else-branch: 27 | curr@72@11 != HeadLeftPost@41@11]
(assert (not (= curr@72@11 HeadLeftPost@41@11)))
; [eval] curr == HeadRightPre
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not (not (or (= curr@72@11 HeadLeftPost@41@11) (= curr@72@11 HeadRightPost@40@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (or (= curr@72@11 HeadLeftPost@41@11) (= curr@72@11 HeadRightPost@40@11))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 28 | curr@72@11 == HeadLeftPost@41@11 || curr@72@11 == HeadRightPost@40@11 | live]
; [else-branch: 28 | !(curr@72@11 == HeadLeftPost@41@11 || curr@72@11 == HeadRightPost@40@11) | dead]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 28 | curr@72@11 == HeadLeftPost@41@11 || curr@72@11 == HeadRightPost@40@11]
(assert (or (= curr@72@11 HeadLeftPost@41@11) (= curr@72@11 HeadRightPost@40@11)))
(pop) ; 9
(pop) ; 8
; Joined path conditions
(assert (or (= curr@72@11 HeadLeftPost@41@11) (= curr@72@11 HeadRightPost@40@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (=>
  (not
    (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11)))
  (and
    (not
      (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11)))
    (or (= curr@72@11 HeadLeftPost@41@11) (= curr@72@11 HeadRightPost@40@11)))))
(assert (or
  (not
    (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11)))
  (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11))))
(declare-const curr__globalInflowPre@111@11 Int)
(assert (=
  curr__globalInflowPre@111@11
  (ite
    (and (= curr@72@11 HeadRightPost@40@11) (= curr@72@11 HeadLeftPost@41@11))
    2
    1)))
; [exec]
; curr__globalInflowPost := (curr == HeadLeftPost && curr == HeadRightPost ?
;     2 :
;     (curr == HeadLeftPost || curr == HeadRightPost ? 1 : 0))
; [eval] (curr == HeadLeftPost && curr == HeadRightPost ? 2 : (curr == HeadLeftPost || curr == HeadRightPost ? 1 : 0))
; [eval] curr == HeadLeftPost && curr == HeadRightPost
; [eval] curr == HeadLeftPost
(push) ; 6
; [then-branch: 29 | curr@72@11 == curr__next_pre@73@11 | live]
; [else-branch: 29 | curr@72@11 != curr__next_pre@73@11 | live]
(push) ; 7
; [then-branch: 29 | curr@72@11 == curr__next_pre@73@11]
(assert (= curr@72@11 curr__next_pre@73@11))
; [eval] curr == HeadRightPost
(pop) ; 7
(push) ; 7
; [else-branch: 29 | curr@72@11 != curr__next_pre@73@11]
(assert (not (= curr@72@11 curr__next_pre@73@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= curr@72@11 curr__next_pre@73@11))
  (= curr@72@11 curr__next_pre@73@11)))
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (= curr@72@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (= curr@72@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 30 | curr@72@11 == curr__next_pre@73@11 | live]
; [else-branch: 30 | curr@72@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 30 | curr@72@11 == curr__next_pre@73@11]
(assert (= curr@72@11 curr__next_pre@73@11))
(pop) ; 7
(push) ; 7
; [else-branch: 30 | curr@72@11 != curr__next_pre@73@11]
(assert (not (= curr@72@11 curr__next_pre@73@11)))
; [eval] (curr == HeadLeftPost || curr == HeadRightPost ? 1 : 0)
; [eval] curr == HeadLeftPost || curr == HeadRightPost
; [eval] curr == HeadLeftPost
(push) ; 8
; [then-branch: 31 | curr@72@11 == curr__next_pre@73@11 | live]
; [else-branch: 31 | curr@72@11 != curr__next_pre@73@11 | live]
(push) ; 9
; [then-branch: 31 | curr@72@11 == curr__next_pre@73@11]
(assert (= curr@72@11 curr__next_pre@73@11))
(pop) ; 9
(push) ; 9
; [else-branch: 31 | curr@72@11 != curr__next_pre@73@11]
; [eval] curr == HeadRightPost
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 32 | True | live]
; [else-branch: 32 | False | dead]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 32 | True]
(pop) ; 9
(pop) ; 8
; Joined path conditions
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(declare-const curr__globalInflowPost@112@11 Int)
(assert (= curr__globalInflowPost@112@11 (ite (= curr@72@11 curr__next_pre@73@11) 2 1)))
; [exec]
; succ__externalInflow := nondet()
(declare-const res@113@11 Int)
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
; [exec]
; inhale succ__externalInflow >= 0
(declare-const $t@114@11 $Snap)
(assert (= $t@114@11 $Snap.unit))
; [eval] succ__externalInflow >= 0
(assert (>= res@113@11 0))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; succ__globalInflowPre := (succ == HeadLeftPre && succ == HeadRightPre ?
;     2 :
;     (succ == HeadLeftPre || succ == HeadRightPre ? 1 : 0))
; [eval] (succ == HeadLeftPre && succ == HeadRightPre ? 2 : (succ == HeadLeftPre || succ == HeadRightPre ? 1 : 0))
; [eval] succ == HeadLeftPre && succ == HeadRightPre
; [eval] succ == HeadLeftPre
(set-option :timeout 0)
(push) ; 6
; [then-branch: 33 | curr__next_pre@73@11 == HeadLeftPost@41@11 | live]
; [else-branch: 33 | curr__next_pre@73@11 != HeadLeftPost@41@11 | live]
(push) ; 7
; [then-branch: 33 | curr__next_pre@73@11 == HeadLeftPost@41@11]
(assert (= curr__next_pre@73@11 HeadLeftPost@41@11))
; [eval] succ == HeadRightPre
(pop) ; 7
(push) ; 7
; [else-branch: 33 | curr__next_pre@73@11 != HeadLeftPost@41@11]
(assert (not (= curr__next_pre@73@11 HeadLeftPost@41@11)))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= curr__next_pre@73@11 HeadLeftPost@41@11))
  (= curr__next_pre@73@11 HeadLeftPost@41@11)))
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not
  (and
    (= curr__next_pre@73@11 HeadRightPost@40@11)
    (= curr__next_pre@73@11 HeadLeftPost@41@11)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (and
  (= curr__next_pre@73@11 HeadRightPost@40@11)
  (= curr__next_pre@73@11 HeadLeftPost@41@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 34 | curr__next_pre@73@11 == HeadRightPost@40@11 && curr__next_pre@73@11 == HeadLeftPost@41@11 | live]
; [else-branch: 34 | !(curr__next_pre@73@11 == HeadRightPost@40@11 && curr__next_pre@73@11 == HeadLeftPost@41@11) | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 34 | curr__next_pre@73@11 == HeadRightPost@40@11 && curr__next_pre@73@11 == HeadLeftPost@41@11]
(assert (and
  (= curr__next_pre@73@11 HeadRightPost@40@11)
  (= curr__next_pre@73@11 HeadLeftPost@41@11)))
(pop) ; 7
(push) ; 7
; [else-branch: 34 | !(curr__next_pre@73@11 == HeadRightPost@40@11 && curr__next_pre@73@11 == HeadLeftPost@41@11)]
(assert (not
  (and
    (= curr__next_pre@73@11 HeadRightPost@40@11)
    (= curr__next_pre@73@11 HeadLeftPost@41@11))))
; [eval] (succ == HeadLeftPre || succ == HeadRightPre ? 1 : 0)
; [eval] succ == HeadLeftPre || succ == HeadRightPre
; [eval] succ == HeadLeftPre
(push) ; 8
; [then-branch: 35 | curr__next_pre@73@11 == HeadLeftPost@41@11 | live]
; [else-branch: 35 | curr__next_pre@73@11 != HeadLeftPost@41@11 | live]
(push) ; 9
; [then-branch: 35 | curr__next_pre@73@11 == HeadLeftPost@41@11]
(assert (= curr__next_pre@73@11 HeadLeftPost@41@11))
(pop) ; 9
(push) ; 9
; [else-branch: 35 | curr__next_pre@73@11 != HeadLeftPost@41@11]
(assert (not (= curr__next_pre@73@11 HeadLeftPost@41@11)))
; [eval] succ == HeadRightPre
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not (not
  (or
    (= curr__next_pre@73@11 HeadLeftPost@41@11)
    (= curr__next_pre@73@11 HeadRightPost@40@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (or
  (= curr__next_pre@73@11 HeadLeftPost@41@11)
  (= curr__next_pre@73@11 HeadRightPost@40@11))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 36 | curr__next_pre@73@11 == HeadLeftPost@41@11 || curr__next_pre@73@11 == HeadRightPost@40@11 | live]
; [else-branch: 36 | !(curr__next_pre@73@11 == HeadLeftPost@41@11 || curr__next_pre@73@11 == HeadRightPost@40@11) | live]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 36 | curr__next_pre@73@11 == HeadLeftPost@41@11 || curr__next_pre@73@11 == HeadRightPost@40@11]
(assert (or
  (= curr__next_pre@73@11 HeadLeftPost@41@11)
  (= curr__next_pre@73@11 HeadRightPost@40@11)))
(pop) ; 9
(push) ; 9
; [else-branch: 36 | !(curr__next_pre@73@11 == HeadLeftPost@41@11 || curr__next_pre@73@11 == HeadRightPost@40@11)]
(assert (not
  (or
    (= curr__next_pre@73@11 HeadLeftPost@41@11)
    (= curr__next_pre@73@11 HeadRightPost@40@11))))
(pop) ; 9
(pop) ; 8
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (or
      (= curr__next_pre@73@11 HeadLeftPost@41@11)
      (= curr__next_pre@73@11 HeadRightPost@40@11)))
  (or
    (= curr__next_pre@73@11 HeadLeftPost@41@11)
    (= curr__next_pre@73@11 HeadRightPost@40@11))))
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (=>
  (not
    (and
      (= curr__next_pre@73@11 HeadRightPost@40@11)
      (= curr__next_pre@73@11 HeadLeftPost@41@11)))
  (and
    (not
      (and
        (= curr__next_pre@73@11 HeadRightPost@40@11)
        (= curr__next_pre@73@11 HeadLeftPost@41@11)))
    (or
      (not
        (or
          (= curr__next_pre@73@11 HeadLeftPost@41@11)
          (= curr__next_pre@73@11 HeadRightPost@40@11)))
      (or
        (= curr__next_pre@73@11 HeadLeftPost@41@11)
        (= curr__next_pre@73@11 HeadRightPost@40@11))))))
(assert (or
  (not
    (and
      (= curr__next_pre@73@11 HeadRightPost@40@11)
      (= curr__next_pre@73@11 HeadLeftPost@41@11)))
  (and
    (= curr__next_pre@73@11 HeadRightPost@40@11)
    (= curr__next_pre@73@11 HeadLeftPost@41@11))))
(declare-const succ__globalInflowPre@115@11 Int)
(assert (=
  succ__globalInflowPre@115@11
  (ite
    (and
      (= curr__next_pre@73@11 HeadRightPost@40@11)
      (= curr__next_pre@73@11 HeadLeftPost@41@11))
    2
    (ite
      (or
        (= curr__next_pre@73@11 HeadLeftPost@41@11)
        (= curr__next_pre@73@11 HeadRightPost@40@11))
      1
      0))))
; [exec]
; succ__globalInflowPost := (succ == HeadLeftPost && succ == HeadRightPost ?
;     2 :
;     (succ == HeadLeftPost || succ == HeadRightPost ? 1 : 0))
; [eval] (succ == HeadLeftPost && succ == HeadRightPost ? 2 : (succ == HeadLeftPost || succ == HeadRightPost ? 1 : 0))
; [eval] succ == HeadLeftPost && succ == HeadRightPost
; [eval] succ == HeadLeftPost
(push) ; 6
; [then-branch: 37 | True | live]
; [else-branch: 37 | False | live]
(push) ; 7
; [then-branch: 37 | True]
; [eval] succ == HeadRightPost
(pop) ; 7
(push) ; 7
; [else-branch: 37 | False]
(assert false)
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(push) ; 6
(push) ; 7
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [then-branch: 38 | curr__next_pre@73@11 == curr@72@11 | live]
; [else-branch: 38 | curr__next_pre@73@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 7
; [then-branch: 38 | curr__next_pre@73@11 == curr@72@11]
(assert (= curr__next_pre@73@11 curr@72@11))
(pop) ; 7
(push) ; 7
; [else-branch: 38 | curr__next_pre@73@11 != curr@72@11]
(assert (not (= curr__next_pre@73@11 curr@72@11)))
; [eval] (succ == HeadLeftPost || succ == HeadRightPost ? 1 : 0)
; [eval] succ == HeadLeftPost || succ == HeadRightPost
; [eval] succ == HeadLeftPost
(push) ; 8
(push) ; 9
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 39 | True | live]
; [else-branch: 39 | False | dead]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 39 | True]
(pop) ; 9
(pop) ; 8
; Joined path conditions
(pop) ; 7
(pop) ; 6
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= curr__next_pre@73@11 curr@72@11))
  (= curr__next_pre@73@11 curr@72@11)))
(declare-const succ__globalInflowPost@116@11 Int)
(assert (= succ__globalInflowPost@116@11 (ite (= curr__next_pre@73@11 curr@72@11) 2 1)))
; [exec]
; new_prev_flow_pre := 0
; [exec]
; new_curr_flow_pre := 0
; [exec]
; new_succ_flow_pre := 0
; [exec]
; fixpoint1 := false
(declare-const new_prev_flow_pre2@117@11 Int)
(declare-const new_curr_flow_pre2@118@11 Int)
(declare-const new_succ_flow_pre2@119@11 Int)
(declare-const fixpoint1@120@11 Bool)
(declare-const new_prev_flow_pre@121@11 Int)
(declare-const new_curr_flow_pre@122@11 Int)
(declare-const new_succ_flow_pre@123@11 Int)
(push) ; 6
; Loop head block: Check well-definedness of invariant
(declare-const $t@124@11 $Snap)
(assert (= $t@124@11 $Snap.unit))
; [eval] fixpoint1 ==> new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
(push) ; 7
(push) ; 8
(set-option :timeout 10)
(assert (not (not fixpoint1@120@11)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(set-option :timeout 10)
(assert (not fixpoint1@120@11))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [then-branch: 40 | fixpoint1@120@11 | live]
; [else-branch: 40 | !(fixpoint1@120@11) | live]
(set-option :timeout 0)
(push) ; 8
; [then-branch: 40 | fixpoint1@120@11]
(assert fixpoint1@120@11)
; [eval] new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
; [eval] new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre
; [eval] (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 41 | prev__next_pre@70@11 == prev@69@11 | live]
; [else-branch: 41 | prev__next_pre@70@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 41 | prev__next_pre@70@11 == prev@69@11]
(assert (= prev__next_pre@70@11 prev@69@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 42 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 42 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 42 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 42 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 41 | prev__next_pre@70@11 != prev@69@11]
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 prev@69@11)
  (and
    (= prev__next_pre@70@11 prev@69@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 prev@69@11))
  (= prev__next_pre@70@11 prev@69@11)))
; [eval] (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 43 | curr__next_pre@73@11 == prev@69@11 | live]
; [else-branch: 43 | curr__next_pre@73@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 43 | curr__next_pre@73@11 == prev@69@11]
(assert (= curr__next_pre@73@11 prev@69@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 44 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 44 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 44 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 44 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 43 | curr__next_pre@73@11 != prev@69@11]
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= curr__next_pre@73@11 prev@69@11)
  (and
    (= curr__next_pre@73@11 prev@69@11)
    (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))))
; Joined path conditions
(assert (or
  (not (= curr__next_pre@73@11 prev@69@11))
  (= curr__next_pre@73@11 prev@69@11)))
; [eval] (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 45 | res@94@11 == prev@69@11 | live]
; [else-branch: 45 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 45 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 46 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 46 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 46 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 46 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 45 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= res@94@11 prev@69@11)
  (and
    (= res@94@11 prev@69@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11)))
(push) ; 9
; [then-branch: 47 | new_prev_flow_pre@121@11 == res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
; [else-branch: 47 | new_prev_flow_pre@121@11 != res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
(push) ; 10
; [then-branch: 47 | new_prev_flow_pre@121@11 == res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (=
  new_prev_flow_pre@121@11
  (+
    (+
      (+
        (+ res@105@11 prev__globalInflowPre@107@11)
        (ite
          (= prev__next_pre@70@11 prev@69@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 prev@69@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 prev@69@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [eval] new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre
; [eval] (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == curr
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 48 | prev__next_pre@70@11 == curr@72@11 | live]
; [else-branch: 48 | prev__next_pre@70@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 48 | prev__next_pre@70@11 == curr@72@11]
(assert (= prev__next_pre@70@11 curr@72@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 14
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 49 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 49 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 49 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 14
(push) ; 14
; [else-branch: 49 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 12
(push) ; 12
; [else-branch: 48 | prev__next_pre@70@11 != curr@72@11]
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr@72@11)
  (and
    (= prev__next_pre@70@11 curr@72@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr@72@11))
  (= prev__next_pre@70@11 curr@72@11)))
; [eval] (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == curr
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 50 | curr__next_pre@73@11 == curr@72@11 | live]
; [else-branch: 50 | curr__next_pre@73@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 50 | curr__next_pre@73@11 == curr@72@11]
(assert (= curr__next_pre@73@11 curr@72@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 14
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 51 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 51 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 51 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 14
(push) ; 14
; [else-branch: 51 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 12
(push) ; 12
; [else-branch: 50 | curr__next_pre@73@11 != curr@72@11]
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
(assert (=>
  (= curr__next_pre@73@11 curr@72@11)
  (and
    (= curr__next_pre@73@11 curr@72@11)
    (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))))
; Joined path conditions
; [eval] (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == curr
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (= res@94@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 52 | res@94@11 == curr@72@11 | live]
; [else-branch: 52 | res@94@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 52 | res@94@11 == curr@72@11]
(assert (= res@94@11 curr@72@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 14
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 53 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 53 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 53 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 14
(push) ; 14
; [else-branch: 53 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 12
(push) ; 12
; [else-branch: 52 | res@94@11 != curr@72@11]
(assert (not (= res@94@11 curr@72@11)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
(assert (=>
  (= res@94@11 curr@72@11)
  (and
    (= res@94@11 curr@72@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 curr@72@11)) (= res@94@11 curr@72@11)))
(push) ; 11
; [then-branch: 54 | new_curr_flow_pre@122@11 == res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
; [else-branch: 54 | new_curr_flow_pre@122@11 != res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
(push) ; 12
; [then-branch: 54 | new_curr_flow_pre@122@11 == res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (=
  new_curr_flow_pre@122@11
  (+
    (+
      (+
        (+ res@109@11 curr__globalInflowPre@111@11)
        (ite
          (= prev__next_pre@70@11 curr@72@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 curr@72@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 curr@72@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [eval] new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre
; [eval] (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == succ
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 14
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 55 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 55 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 55 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 15
(push) ; 16
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 16
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
; [then-branch: 56 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 56 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 16
; [then-branch: 56 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 16
(push) ; 16
; [else-branch: 56 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 16
(pop) ; 15
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 14
(push) ; 14
; [else-branch: 55 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr__next_pre@73@11)
  (and
    (= prev__next_pre@70@11 curr__next_pre@73@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr__next_pre@73@11))
  (= prev__next_pre@70@11 curr__next_pre@73@11)))
; [eval] (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == succ
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 57 | True | live]
; [else-branch: 57 | False | dead]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 57 | True]
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 15
(push) ; 16
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 16
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
; [then-branch: 58 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 58 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 16
; [then-branch: 58 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 16
(push) ; 16
; [else-branch: 58 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 16
(pop) ; 15
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
; [eval] (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == succ
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 14
(set-option :timeout 10)
(assert (not (= res@94@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 59 | res@94@11 == curr__next_pre@73@11 | live]
; [else-branch: 59 | res@94@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 59 | res@94@11 == curr__next_pre@73@11]
(assert (= res@94@11 curr__next_pre@73@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 15
(push) ; 16
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 16
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
; [then-branch: 60 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 60 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 16
; [then-branch: 60 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 16
(push) ; 16
; [else-branch: 60 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 16
(pop) ; 15
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 14
(push) ; 14
; [else-branch: 59 | res@94@11 != curr__next_pre@73@11]
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 14
(pop) ; 13
; Joined path conditions
(assert (=>
  (= res@94@11 curr__next_pre@73@11)
  (and
    (= res@94@11 curr__next_pre@73@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 curr__next_pre@73@11)) (= res@94@11 curr__next_pre@73@11)))
(pop) ; 12
(push) ; 12
; [else-branch: 54 | new_curr_flow_pre@122@11 != res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (not
  (=
    new_curr_flow_pre@122@11
    (+
      (+
        (+
          (+ res@109@11 curr__globalInflowPre@111@11)
          (ite
            (= prev__next_pre@70@11 curr@72@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 curr@72@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 curr@72@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 12
(pop) ; 11
; Joined path conditions
(assert (=>
  (=
    new_curr_flow_pre@122@11
    (+
      (+
        (+
          (+ res@109@11 curr__globalInflowPre@111@11)
          (ite
            (= prev__next_pre@70@11 curr@72@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 curr@72@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 curr@72@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))
  (and
    (=
      new_curr_flow_pre@122@11
      (+
        (+
          (+
            (+ res@109@11 curr__globalInflowPre@111@11)
            (ite
              (= prev__next_pre@70@11 curr@72@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 curr@72@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 curr@72@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (=>
      (= prev__next_pre@70@11 curr__next_pre@73@11)
      (and
        (= prev__next_pre@70@11 curr__next_pre@73@11)
        (or
          (not (>= new_prev_flow_pre@121@11 3))
          (>= new_prev_flow_pre@121@11 3))))
    (or
      (not (= prev__next_pre@70@11 curr__next_pre@73@11))
      (= prev__next_pre@70@11 curr__next_pre@73@11))
    (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3))
    (=>
      (= res@94@11 curr__next_pre@73@11)
      (and
        (= res@94@11 curr__next_pre@73@11)
        (or
          (not (>= new_succ_flow_pre@123@11 3))
          (>= new_succ_flow_pre@123@11 3))))
    (or
      (not (= res@94@11 curr__next_pre@73@11))
      (= res@94@11 curr__next_pre@73@11)))))
; Joined path conditions
(assert (or
  (not
    (=
      new_curr_flow_pre@122@11
      (+
        (+
          (+
            (+ res@109@11 curr__globalInflowPre@111@11)
            (ite
              (= prev__next_pre@70@11 curr@72@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 curr@72@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 curr@72@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_curr_flow_pre@122@11
    (+
      (+
        (+
          (+ res@109@11 curr__globalInflowPre@111@11)
          (ite
            (= prev__next_pre@70@11 curr@72@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 curr@72@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 curr@72@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 10
(push) ; 10
; [else-branch: 47 | new_prev_flow_pre@121@11 != res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (not
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))
  (and
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (=>
      (= prev__next_pre@70@11 curr@72@11)
      (and
        (= prev__next_pre@70@11 curr@72@11)
        (or
          (not (>= new_prev_flow_pre@121@11 3))
          (>= new_prev_flow_pre@121@11 3))))
    (or
      (not (= prev__next_pre@70@11 curr@72@11))
      (= prev__next_pre@70@11 curr@72@11))
    (=>
      (= curr__next_pre@73@11 curr@72@11)
      (and
        (= curr__next_pre@73@11 curr@72@11)
        (or
          (not (>= new_curr_flow_pre@122@11 3))
          (>= new_curr_flow_pre@122@11 3))))
    (=>
      (= res@94@11 curr@72@11)
      (and
        (= res@94@11 curr@72@11)
        (or
          (not (>= new_succ_flow_pre@123@11 3))
          (>= new_succ_flow_pre@123@11 3))))
    (or (not (= res@94@11 curr@72@11)) (= res@94@11 curr@72@11))
    (=>
      (=
        new_curr_flow_pre@122@11
        (+
          (+
            (+
              (+ res@109@11 curr__globalInflowPre@111@11)
              (ite
                (= prev__next_pre@70@11 curr@72@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 curr@72@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 curr@72@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (and
        (=
          new_curr_flow_pre@122@11
          (+
            (+
              (+
                (+ res@109@11 curr__globalInflowPre@111@11)
                (ite
                  (= prev__next_pre@70@11 curr@72@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 curr@72@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 curr@72@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0)))
        (=>
          (= prev__next_pre@70@11 curr__next_pre@73@11)
          (and
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            (or
              (not (>= new_prev_flow_pre@121@11 3))
              (>= new_prev_flow_pre@121@11 3))))
        (or
          (not (= prev__next_pre@70@11 curr__next_pre@73@11))
          (= prev__next_pre@70@11 curr__next_pre@73@11))
        (or
          (not (>= new_curr_flow_pre@122@11 3))
          (>= new_curr_flow_pre@122@11 3))
        (=>
          (= res@94@11 curr__next_pre@73@11)
          (and
            (= res@94@11 curr__next_pre@73@11)
            (or
              (not (>= new_succ_flow_pre@123@11 3))
              (>= new_succ_flow_pre@123@11 3))))
        (or
          (not (= res@94@11 curr__next_pre@73@11))
          (= res@94@11 curr__next_pre@73@11))))
    (or
      (not
        (=
          new_curr_flow_pre@122@11
          (+
            (+
              (+
                (+ res@109@11 curr__globalInflowPre@111@11)
                (ite
                  (= prev__next_pre@70@11 curr@72@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 curr@72@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 curr@72@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0))))
      (=
        new_curr_flow_pre@122@11
        (+
          (+
            (+
              (+ res@109@11 curr__globalInflowPre@111@11)
              (ite
                (= prev__next_pre@70@11 curr@72@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 curr@72@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 curr@72@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))))))
; Joined path conditions
(assert (or
  (not
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 8
(push) ; 8
; [else-branch: 40 | !(fixpoint1@120@11)]
(assert (not fixpoint1@120@11))
(pop) ; 8
(pop) ; 7
; Joined path conditions
(assert (=>
  fixpoint1@120@11
  (and
    fixpoint1@120@11
    (=>
      (= prev__next_pre@70@11 prev@69@11)
      (and
        (= prev__next_pre@70@11 prev@69@11)
        (or
          (not (>= new_prev_flow_pre@121@11 3))
          (>= new_prev_flow_pre@121@11 3))))
    (or
      (not (= prev__next_pre@70@11 prev@69@11))
      (= prev__next_pre@70@11 prev@69@11))
    (=>
      (= curr__next_pre@73@11 prev@69@11)
      (and
        (= curr__next_pre@73@11 prev@69@11)
        (or
          (not (>= new_curr_flow_pre@122@11 3))
          (>= new_curr_flow_pre@122@11 3))))
    (or
      (not (= curr__next_pre@73@11 prev@69@11))
      (= curr__next_pre@73@11 prev@69@11))
    (=>
      (= res@94@11 prev@69@11)
      (and
        (= res@94@11 prev@69@11)
        (or
          (not (>= new_succ_flow_pre@123@11 3))
          (>= new_succ_flow_pre@123@11 3))))
    (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11))
    (=>
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (and
        (=
          new_prev_flow_pre@121@11
          (+
            (+
              (+
                (+ res@105@11 prev__globalInflowPre@107@11)
                (ite
                  (= prev__next_pre@70@11 prev@69@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 prev@69@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0)))
        (=>
          (= prev__next_pre@70@11 curr@72@11)
          (and
            (= prev__next_pre@70@11 curr@72@11)
            (or
              (not (>= new_prev_flow_pre@121@11 3))
              (>= new_prev_flow_pre@121@11 3))))
        (or
          (not (= prev__next_pre@70@11 curr@72@11))
          (= prev__next_pre@70@11 curr@72@11))
        (=>
          (= curr__next_pre@73@11 curr@72@11)
          (and
            (= curr__next_pre@73@11 curr@72@11)
            (or
              (not (>= new_curr_flow_pre@122@11 3))
              (>= new_curr_flow_pre@122@11 3))))
        (=>
          (= res@94@11 curr@72@11)
          (and
            (= res@94@11 curr@72@11)
            (or
              (not (>= new_succ_flow_pre@123@11 3))
              (>= new_succ_flow_pre@123@11 3))))
        (or (not (= res@94@11 curr@72@11)) (= res@94@11 curr@72@11))
        (=>
          (=
            new_curr_flow_pre@122@11
            (+
              (+
                (+
                  (+ res@109@11 curr__globalInflowPre@111@11)
                  (ite
                    (= prev__next_pre@70@11 curr@72@11)
                    (ite
                      (>= new_prev_flow_pre@121@11 3)
                      3
                      new_prev_flow_pre@121@11)
                    0))
                (ite
                  (= curr__next_pre@73@11 curr@72@11)
                  (ite
                    (>= new_curr_flow_pre@122@11 3)
                    3
                    new_curr_flow_pre@122@11)
                  0))
              (ite
                (= res@94@11 curr@72@11)
                (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
                0)))
          (and
            (=
              new_curr_flow_pre@122@11
              (+
                (+
                  (+
                    (+ res@109@11 curr__globalInflowPre@111@11)
                    (ite
                      (= prev__next_pre@70@11 curr@72@11)
                      (ite
                        (>= new_prev_flow_pre@121@11 3)
                        3
                        new_prev_flow_pre@121@11)
                      0))
                  (ite
                    (= curr__next_pre@73@11 curr@72@11)
                    (ite
                      (>= new_curr_flow_pre@122@11 3)
                      3
                      new_curr_flow_pre@122@11)
                    0))
                (ite
                  (= res@94@11 curr@72@11)
                  (ite
                    (>= new_succ_flow_pre@123@11 3)
                    3
                    new_succ_flow_pre@123@11)
                  0)))
            (=>
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (and
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (or
                  (not (>= new_prev_flow_pre@121@11 3))
                  (>= new_prev_flow_pre@121@11 3))))
            (or
              (not (= prev__next_pre@70@11 curr__next_pre@73@11))
              (= prev__next_pre@70@11 curr__next_pre@73@11))
            (or
              (not (>= new_curr_flow_pre@122@11 3))
              (>= new_curr_flow_pre@122@11 3))
            (=>
              (= res@94@11 curr__next_pre@73@11)
              (and
                (= res@94@11 curr__next_pre@73@11)
                (or
                  (not (>= new_succ_flow_pre@123@11 3))
                  (>= new_succ_flow_pre@123@11 3))))
            (or
              (not (= res@94@11 curr__next_pre@73@11))
              (= res@94@11 curr__next_pre@73@11))))
        (or
          (not
            (=
              new_curr_flow_pre@122@11
              (+
                (+
                  (+
                    (+ res@109@11 curr__globalInflowPre@111@11)
                    (ite
                      (= prev__next_pre@70@11 curr@72@11)
                      (ite
                        (>= new_prev_flow_pre@121@11 3)
                        3
                        new_prev_flow_pre@121@11)
                      0))
                  (ite
                    (= curr__next_pre@73@11 curr@72@11)
                    (ite
                      (>= new_curr_flow_pre@122@11 3)
                      3
                      new_curr_flow_pre@122@11)
                    0))
                (ite
                  (= res@94@11 curr@72@11)
                  (ite
                    (>= new_succ_flow_pre@123@11 3)
                    3
                    new_succ_flow_pre@123@11)
                  0))))
          (=
            new_curr_flow_pre@122@11
            (+
              (+
                (+
                  (+ res@109@11 curr__globalInflowPre@111@11)
                  (ite
                    (= prev__next_pre@70@11 curr@72@11)
                    (ite
                      (>= new_prev_flow_pre@121@11 3)
                      3
                      new_prev_flow_pre@121@11)
                    0))
                (ite
                  (= curr__next_pre@73@11 curr@72@11)
                  (ite
                    (>= new_curr_flow_pre@122@11 3)
                    3
                    new_curr_flow_pre@122@11)
                  0))
              (ite
                (= res@94@11 curr@72@11)
                (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
                0))))))
    (or
      (not
        (=
          new_prev_flow_pre@121@11
          (+
            (+
              (+
                (+ res@105@11 prev__globalInflowPre@107@11)
                (ite
                  (= prev__next_pre@70@11 prev@69@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 prev@69@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0))))
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))))))
; Joined path conditions
(assert (or (not fixpoint1@120@11) fixpoint1@120@11))
(assert (=>
  fixpoint1@120@11
  (and
    (and
      (=
        new_succ_flow_pre@123@11
        (+
          (+
            (+
              (+ res@113@11 succ__globalInflowPre@115@11)
              (ite
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11))
          (ite
            (= res@94@11 curr__next_pre@73@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (=
        new_curr_flow_pre@122@11
        (+
          (+
            (+
              (+ res@109@11 curr__globalInflowPre@111@11)
              (ite
                (= prev__next_pre@70@11 curr@72@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 curr@72@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 curr@72@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0))))
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))))
; Loop head block: Check well-definedness of edge conditions
(push) ; 7
; [eval] !fixpoint1
(pop) ; 7
(push) ; 7
; [eval] !!fixpoint1
; [eval] !fixpoint1
(pop) ; 7
(pop) ; 6
(push) ; 6
; Loop head block: Establish invariant
; [eval] fixpoint1 ==> new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
(push) ; 7
; [then-branch: 61 | False | dead]
; [else-branch: 61 | True | live]
(push) ; 8
; [else-branch: 61 | True]
(pop) ; 8
(pop) ; 7
; Joined path conditions
; Loop head block: Execute statements of loop head block (in invariant state)
(push) ; 7
(assert (= $t@124@11 $Snap.unit))
(assert (=>
  fixpoint1@120@11
  (and
    fixpoint1@120@11
    (=>
      (= prev__next_pre@70@11 prev@69@11)
      (and
        (= prev__next_pre@70@11 prev@69@11)
        (or
          (not (>= new_prev_flow_pre@121@11 3))
          (>= new_prev_flow_pre@121@11 3))))
    (or
      (not (= prev__next_pre@70@11 prev@69@11))
      (= prev__next_pre@70@11 prev@69@11))
    (=>
      (= curr__next_pre@73@11 prev@69@11)
      (and
        (= curr__next_pre@73@11 prev@69@11)
        (or
          (not (>= new_curr_flow_pre@122@11 3))
          (>= new_curr_flow_pre@122@11 3))))
    (or
      (not (= curr__next_pre@73@11 prev@69@11))
      (= curr__next_pre@73@11 prev@69@11))
    (=>
      (= res@94@11 prev@69@11)
      (and
        (= res@94@11 prev@69@11)
        (or
          (not (>= new_succ_flow_pre@123@11 3))
          (>= new_succ_flow_pre@123@11 3))))
    (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11))
    (=>
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (and
        (=
          new_prev_flow_pre@121@11
          (+
            (+
              (+
                (+ res@105@11 prev__globalInflowPre@107@11)
                (ite
                  (= prev__next_pre@70@11 prev@69@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 prev@69@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0)))
        (=>
          (= prev__next_pre@70@11 curr@72@11)
          (and
            (= prev__next_pre@70@11 curr@72@11)
            (or
              (not (>= new_prev_flow_pre@121@11 3))
              (>= new_prev_flow_pre@121@11 3))))
        (or
          (not (= prev__next_pre@70@11 curr@72@11))
          (= prev__next_pre@70@11 curr@72@11))
        (=>
          (= curr__next_pre@73@11 curr@72@11)
          (and
            (= curr__next_pre@73@11 curr@72@11)
            (or
              (not (>= new_curr_flow_pre@122@11 3))
              (>= new_curr_flow_pre@122@11 3))))
        (=>
          (= res@94@11 curr@72@11)
          (and
            (= res@94@11 curr@72@11)
            (or
              (not (>= new_succ_flow_pre@123@11 3))
              (>= new_succ_flow_pre@123@11 3))))
        (or (not (= res@94@11 curr@72@11)) (= res@94@11 curr@72@11))
        (=>
          (=
            new_curr_flow_pre@122@11
            (+
              (+
                (+
                  (+ res@109@11 curr__globalInflowPre@111@11)
                  (ite
                    (= prev__next_pre@70@11 curr@72@11)
                    (ite
                      (>= new_prev_flow_pre@121@11 3)
                      3
                      new_prev_flow_pre@121@11)
                    0))
                (ite
                  (= curr__next_pre@73@11 curr@72@11)
                  (ite
                    (>= new_curr_flow_pre@122@11 3)
                    3
                    new_curr_flow_pre@122@11)
                  0))
              (ite
                (= res@94@11 curr@72@11)
                (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
                0)))
          (and
            (=
              new_curr_flow_pre@122@11
              (+
                (+
                  (+
                    (+ res@109@11 curr__globalInflowPre@111@11)
                    (ite
                      (= prev__next_pre@70@11 curr@72@11)
                      (ite
                        (>= new_prev_flow_pre@121@11 3)
                        3
                        new_prev_flow_pre@121@11)
                      0))
                  (ite
                    (= curr__next_pre@73@11 curr@72@11)
                    (ite
                      (>= new_curr_flow_pre@122@11 3)
                      3
                      new_curr_flow_pre@122@11)
                    0))
                (ite
                  (= res@94@11 curr@72@11)
                  (ite
                    (>= new_succ_flow_pre@123@11 3)
                    3
                    new_succ_flow_pre@123@11)
                  0)))
            (=>
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (and
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (or
                  (not (>= new_prev_flow_pre@121@11 3))
                  (>= new_prev_flow_pre@121@11 3))))
            (or
              (not (= prev__next_pre@70@11 curr__next_pre@73@11))
              (= prev__next_pre@70@11 curr__next_pre@73@11))
            (or
              (not (>= new_curr_flow_pre@122@11 3))
              (>= new_curr_flow_pre@122@11 3))
            (=>
              (= res@94@11 curr__next_pre@73@11)
              (and
                (= res@94@11 curr__next_pre@73@11)
                (or
                  (not (>= new_succ_flow_pre@123@11 3))
                  (>= new_succ_flow_pre@123@11 3))))
            (or
              (not (= res@94@11 curr__next_pre@73@11))
              (= res@94@11 curr__next_pre@73@11))))
        (or
          (not
            (=
              new_curr_flow_pre@122@11
              (+
                (+
                  (+
                    (+ res@109@11 curr__globalInflowPre@111@11)
                    (ite
                      (= prev__next_pre@70@11 curr@72@11)
                      (ite
                        (>= new_prev_flow_pre@121@11 3)
                        3
                        new_prev_flow_pre@121@11)
                      0))
                  (ite
                    (= curr__next_pre@73@11 curr@72@11)
                    (ite
                      (>= new_curr_flow_pre@122@11 3)
                      3
                      new_curr_flow_pre@122@11)
                    0))
                (ite
                  (= res@94@11 curr@72@11)
                  (ite
                    (>= new_succ_flow_pre@123@11 3)
                    3
                    new_succ_flow_pre@123@11)
                  0))))
          (=
            new_curr_flow_pre@122@11
            (+
              (+
                (+
                  (+ res@109@11 curr__globalInflowPre@111@11)
                  (ite
                    (= prev__next_pre@70@11 curr@72@11)
                    (ite
                      (>= new_prev_flow_pre@121@11 3)
                      3
                      new_prev_flow_pre@121@11)
                    0))
                (ite
                  (= curr__next_pre@73@11 curr@72@11)
                  (ite
                    (>= new_curr_flow_pre@122@11 3)
                    3
                    new_curr_flow_pre@122@11)
                  0))
              (ite
                (= res@94@11 curr@72@11)
                (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
                0))))))
    (or
      (not
        (=
          new_prev_flow_pre@121@11
          (+
            (+
              (+
                (+ res@105@11 prev__globalInflowPre@107@11)
                (ite
                  (= prev__next_pre@70@11 prev@69@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 prev@69@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0))))
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))))))
(assert (or (not fixpoint1@120@11) fixpoint1@120@11))
(assert (=>
  fixpoint1@120@11
  (and
    (and
      (=
        new_succ_flow_pre@123@11
        (+
          (+
            (+
              (+ res@113@11 succ__globalInflowPre@115@11)
              (ite
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11))
          (ite
            (= res@94@11 curr__next_pre@73@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (=
        new_curr_flow_pre@122@11
        (+
          (+
            (+
              (+ res@109@11 curr__globalInflowPre@111@11)
              (ite
                (= prev__next_pre@70@11 curr@72@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 curr@72@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 curr@72@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0))))
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 10)
(check-sat)
; unknown
; Loop head block: Follow loop-internal edges
; [eval] !fixpoint1
(set-option :timeout 0)
(push) ; 8
(set-option :timeout 10)
(assert (not fixpoint1@120@11))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(set-option :timeout 10)
(assert (not (not fixpoint1@120@11)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [then-branch: 62 | !(fixpoint1@120@11) | live]
; [else-branch: 62 | fixpoint1@120@11 | live]
(set-option :timeout 0)
(push) ; 8
; [then-branch: 62 | !(fixpoint1@120@11)]
(assert (not fixpoint1@120@11))
; [exec]
; var new_prev_flow_pre2: Int
(declare-const new_prev_flow_pre2@125@11 Int)
; [exec]
; var new_curr_flow_pre2: Int
(declare-const new_curr_flow_pre2@126@11 Int)
; [exec]
; var new_succ_flow_pre2: Int
(declare-const new_succ_flow_pre2@127@11 Int)
; [exec]
; new_prev_flow_pre2 := prev__externalInflow + prev__globalInflowPre +
;   (prev__next_pre == prev ?
;     (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) :
;     0) +
;   (curr__next_pre == prev ?
;     (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) :
;     0) +
;   (succ__next_pre == prev ?
;     (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) :
;     0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre
; [eval] (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 63 | prev__next_pre@70@11 == prev@69@11 | live]
; [else-branch: 63 | prev__next_pre@70@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 63 | prev__next_pre@70@11 == prev@69@11]
(assert (= prev__next_pre@70@11 prev@69@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 64 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 64 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 64 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 64 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 63 | prev__next_pre@70@11 != prev@69@11]
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 prev@69@11)
  (and
    (= prev__next_pre@70@11 prev@69@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 prev@69@11))
  (= prev__next_pre@70@11 prev@69@11)))
; [eval] (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 65 | curr__next_pre@73@11 == prev@69@11 | live]
; [else-branch: 65 | curr__next_pre@73@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 65 | curr__next_pre@73@11 == prev@69@11]
(assert (= curr__next_pre@73@11 prev@69@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 66 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 66 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 66 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 66 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 65 | curr__next_pre@73@11 != prev@69@11]
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= curr__next_pre@73@11 prev@69@11)
  (and
    (= curr__next_pre@73@11 prev@69@11)
    (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))))
; Joined path conditions
(assert (or
  (not (= curr__next_pre@73@11 prev@69@11))
  (= curr__next_pre@73@11 prev@69@11)))
; [eval] (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == prev
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 67 | res@94@11 == prev@69@11 | live]
; [else-branch: 67 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 67 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 68 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 68 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 68 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 68 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 67 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= res@94@11 prev@69@11)
  (and
    (= res@94@11 prev@69@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11)))
(declare-const new_prev_flow_pre2@128@11 Int)
(assert (=
  new_prev_flow_pre2@128@11
  (+
    (+
      (+
        (+ res@105@11 prev__globalInflowPre@107@11)
        (ite
          (= prev__next_pre@70@11 prev@69@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 prev@69@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 prev@69@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [exec]
; new_curr_flow_pre2 := curr__externalInflow + curr__globalInflowPre +
;   (prev__next_pre == curr ?
;     (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) :
;     0) +
;   (curr__next_pre == curr ?
;     (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) :
;     0) +
;   (succ__next_pre == curr ?
;     (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) :
;     0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre
; [eval] (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == curr
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 69 | prev__next_pre@70@11 == curr@72@11 | live]
; [else-branch: 69 | prev__next_pre@70@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 69 | prev__next_pre@70@11 == curr@72@11]
(assert (= prev__next_pre@70@11 curr@72@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 70 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 70 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 70 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 70 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 69 | prev__next_pre@70@11 != curr@72@11]
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr@72@11)
  (and
    (= prev__next_pre@70@11 curr@72@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr@72@11))
  (= prev__next_pre@70@11 curr@72@11)))
; [eval] (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == curr
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 71 | curr__next_pre@73@11 == curr@72@11 | live]
; [else-branch: 71 | curr__next_pre@73@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 71 | curr__next_pre@73@11 == curr@72@11]
(assert (= curr__next_pre@73@11 curr@72@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 72 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 72 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 72 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 72 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 71 | curr__next_pre@73@11 != curr@72@11]
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= curr__next_pre@73@11 curr@72@11)
  (and
    (= curr__next_pre@73@11 curr@72@11)
    (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))))
; Joined path conditions
; [eval] (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == curr
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= res@94@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 73 | res@94@11 == curr@72@11 | live]
; [else-branch: 73 | res@94@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 73 | res@94@11 == curr@72@11]
(assert (= res@94@11 curr@72@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 74 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 74 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 74 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 74 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 73 | res@94@11 != curr@72@11]
(assert (not (= res@94@11 curr@72@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= res@94@11 curr@72@11)
  (and
    (= res@94@11 curr@72@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 curr@72@11)) (= res@94@11 curr@72@11)))
(declare-const new_curr_flow_pre2@129@11 Int)
(assert (=
  new_curr_flow_pre2@129@11
  (+
    (+
      (+
        (+ res@109@11 curr__globalInflowPre@111@11)
        (ite
          (= prev__next_pre@70@11 curr@72@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 curr@72@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 curr@72@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [exec]
; new_succ_flow_pre2 := succ__externalInflow + succ__globalInflowPre +
;   (prev__next_pre == succ ?
;     (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) :
;     0) +
;   (curr__next_pre == succ ?
;     (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) :
;     0) +
;   (succ__next_pre == succ ?
;     (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) :
;     0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre
; [eval] (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == succ
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 75 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 75 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 75 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 76 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 76 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 76 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 76 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 75 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr__next_pre@73@11)
  (and
    (= prev__next_pre@70@11 curr__next_pre@73@11)
    (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr__next_pre@73@11))
  (= prev__next_pre@70@11 curr__next_pre@73@11)))
; [eval] (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == succ
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 77 | True | live]
; [else-branch: 77 | False | dead]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 77 | True]
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 78 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 78 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 78 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 78 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (or (not (>= new_curr_flow_pre@122@11 3)) (>= new_curr_flow_pre@122@11 3)))
; [eval] (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == succ
(push) ; 9
(push) ; 10
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(set-option :timeout 10)
(assert (not (= res@94@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [then-branch: 79 | res@94@11 == curr__next_pre@73@11 | live]
; [else-branch: 79 | res@94@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 10
; [then-branch: 79 | res@94@11 == curr__next_pre@73@11]
(assert (= res@94@11 curr__next_pre@73@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 11
(push) ; 12
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 80 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 80 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 80 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 12
(push) ; 12
; [else-branch: 80 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 10
(push) ; 10
; [else-branch: 79 | res@94@11 != curr__next_pre@73@11]
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= res@94@11 curr__next_pre@73@11)
  (and
    (= res@94@11 curr__next_pre@73@11)
    (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 curr__next_pre@73@11)) (= res@94@11 curr__next_pre@73@11)))
(declare-const new_succ_flow_pre2@130@11 Int)
(assert (=
  new_succ_flow_pre2@130@11
  (+
    (+
      (+
        (+ res@113@11 succ__globalInflowPre@115@11)
        (ite
          (= prev__next_pre@70@11 curr__next_pre@73@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11))
    (ite
      (= res@94@11 curr__next_pre@73@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [eval] new_prev_flow_pre == new_prev_flow_pre2 && (new_curr_flow_pre == new_curr_flow_pre2 && new_succ_flow_pre == new_succ_flow_pre2)
; [eval] new_prev_flow_pre == new_prev_flow_pre2
(push) ; 9
; [then-branch: 81 | new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11 | live]
; [else-branch: 81 | new_prev_flow_pre@121@11 != new_prev_flow_pre2@128@11 | live]
(push) ; 10
; [then-branch: 81 | new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11]
(assert (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))
; [eval] new_curr_flow_pre == new_curr_flow_pre2
(push) ; 11
; [then-branch: 82 | new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 | live]
; [else-branch: 82 | new_curr_flow_pre@122@11 != new_curr_flow_pre2@129@11 | live]
(push) ; 12
; [then-branch: 82 | new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11]
(assert (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
; [eval] new_succ_flow_pre == new_succ_flow_pre2
(pop) ; 12
(push) ; 12
; [else-branch: 82 | new_curr_flow_pre@122@11 != new_curr_flow_pre2@129@11]
(assert (not (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11)))
(pop) ; 10
(push) ; 10
; [else-branch: 81 | new_prev_flow_pre@121@11 != new_prev_flow_pre2@128@11]
(assert (not (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
(assert (=>
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)
  (and
    (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)
    (or
      (not (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
      (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11)))))
; Joined path conditions
(assert (or
  (not (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))
(push) ; 9
(set-option :timeout 10)
(assert (not (not
  (and
    (and
      (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
      (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
    (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (and
  (and
    (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
    (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 83 | new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11 | live]
; [else-branch: 83 | !(new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11) | live]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 83 | new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11]
(assert (and
  (and
    (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
    (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))
; [exec]
; fixpoint1 := true
; Loop head block: Re-establish invariant
; [eval] fixpoint1 ==> new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
(push) ; 10
(push) ; 11
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [then-branch: 84 | True | live]
; [else-branch: 84 | False | dead]
(set-option :timeout 0)
(push) ; 11
; [then-branch: 84 | True]
; [eval] new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
; [eval] new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__externalInflow + prev__globalInflowPre
; [eval] (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 85 | prev__next_pre@70@11 == prev@69@11 | live]
; [else-branch: 85 | prev__next_pre@70@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 85 | prev__next_pre@70@11 == prev@69@11]
(assert (= prev__next_pre@70@11 prev@69@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 86 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 86 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 86 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 86 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 85 | prev__next_pre@70@11 != prev@69@11]
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [eval] (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 87 | curr__next_pre@73@11 == prev@69@11 | live]
; [else-branch: 87 | curr__next_pre@73@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 87 | curr__next_pre@73@11 == prev@69@11]
(assert (= curr__next_pre@73@11 prev@69@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 88 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 88 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 88 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 88 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(pop) ; 13
(push) ; 13
; [else-branch: 87 | curr__next_pre@73@11 != prev@69@11]
(assert (not (= curr__next_pre@73@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [eval] (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 89 | res@94@11 == prev@69@11 | live]
; [else-branch: 89 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 89 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 90 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 90 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 90 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 90 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 89 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(push) ; 12
; [then-branch: 91 | new_prev_flow_pre@121@11 == res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
; [else-branch: 91 | new_prev_flow_pre@121@11 != res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
(push) ; 13
; [then-branch: 91 | new_prev_flow_pre@121@11 == res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (=
  new_prev_flow_pre@121@11
  (+
    (+
      (+
        (+ res@105@11 prev__globalInflowPre@107@11)
        (ite
          (= prev__next_pre@70@11 prev@69@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 prev@69@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 prev@69@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [eval] new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] curr__externalInflow + curr__globalInflowPre
; [eval] (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 92 | prev__next_pre@70@11 == curr@72@11 | live]
; [else-branch: 92 | prev__next_pre@70@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 92 | prev__next_pre@70@11 == curr@72@11]
(assert (= prev__next_pre@70@11 curr@72@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 93 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 93 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 93 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 17
(push) ; 17
; [else-branch: 93 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 15
(push) ; 15
; [else-branch: 92 | prev__next_pre@70@11 != curr@72@11]
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
; [eval] (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 94 | curr__next_pre@73@11 == curr@72@11 | live]
; [else-branch: 94 | curr__next_pre@73@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 94 | curr__next_pre@73@11 == curr@72@11]
(assert (= curr__next_pre@73@11 curr@72@11))
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 95 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 95 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 95 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 17
(push) ; 17
; [else-branch: 95 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
; Joined path conditions
(pop) ; 15
(push) ; 15
; [else-branch: 94 | curr__next_pre@73@11 != curr@72@11]
(assert (not (= curr__next_pre@73@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
; [eval] (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr@72@11))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (= res@94@11 curr@72@11)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 96 | res@94@11 == curr@72@11 | live]
; [else-branch: 96 | res@94@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 96 | res@94@11 == curr@72@11]
(assert (= res@94@11 curr@72@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 97 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 97 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 97 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 17
(push) ; 17
; [else-branch: 97 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 15
(push) ; 15
; [else-branch: 96 | res@94@11 != curr@72@11]
(assert (not (= res@94@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(push) ; 14
; [then-branch: 98 | new_curr_flow_pre@122@11 == res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
; [else-branch: 98 | new_curr_flow_pre@122@11 != res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0) | live]
(push) ; 15
; [then-branch: 98 | new_curr_flow_pre@122@11 == res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (=
  new_curr_flow_pre@122@11
  (+
    (+
      (+
        (+ res@109@11 curr__globalInflowPre@111@11)
        (ite
          (= prev__next_pre@70@11 curr@72@11)
          (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
          0))
      (ite
        (= curr__next_pre@73@11 curr@72@11)
        (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
        0))
    (ite
      (= res@94@11 curr@72@11)
      (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
      0))))
; [eval] new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] succ__externalInflow + succ__globalInflowPre
; [eval] (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0)
; [eval] prev__next_pre == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 99 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 99 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 99 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre)
; [eval] new_prev_flow_pre >= 3
(push) ; 18
(push) ; 19
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_pre@121@11 3))))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 19
(set-option :timeout 10)
(assert (not (>= new_prev_flow_pre@121@11 3)))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
; [then-branch: 100 | new_prev_flow_pre@121@11 >= 3 | live]
; [else-branch: 100 | !(new_prev_flow_pre@121@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 19
; [then-branch: 100 | new_prev_flow_pre@121@11 >= 3]
(assert (>= new_prev_flow_pre@121@11 3))
(pop) ; 19
(push) ; 19
; [else-branch: 100 | !(new_prev_flow_pre@121@11 >= 3)]
(assert (not (>= new_prev_flow_pre@121@11 3)))
(pop) ; 19
(pop) ; 18
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_pre@121@11 3)) (>= new_prev_flow_pre@121@11 3)))
(pop) ; 17
(push) ; 17
; [else-branch: 99 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
; Joined path conditions
; [eval] (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0)
; [eval] curr__next_pre == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 101 | True | live]
; [else-branch: 101 | False | dead]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 101 | True]
; [eval] (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre)
; [eval] new_curr_flow_pre >= 3
(push) ; 18
(push) ; 19
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_pre@122@11 3))))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 19
(set-option :timeout 10)
(assert (not (>= new_curr_flow_pre@122@11 3)))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
; [then-branch: 102 | new_curr_flow_pre@122@11 >= 3 | live]
; [else-branch: 102 | !(new_curr_flow_pre@122@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 19
; [then-branch: 102 | new_curr_flow_pre@122@11 >= 3]
(assert (>= new_curr_flow_pre@122@11 3))
(pop) ; 19
(push) ; 19
; [else-branch: 102 | !(new_curr_flow_pre@122@11 >= 3)]
(assert (not (>= new_curr_flow_pre@122@11 3)))
(pop) ; 19
(pop) ; 18
; Joined path conditions
; Joined path conditions
(pop) ; 17
(pop) ; 16
; Joined path conditions
; [eval] (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0)
; [eval] succ__next_pre == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (= res@94@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 103 | res@94@11 == curr__next_pre@73@11 | live]
; [else-branch: 103 | res@94@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 103 | res@94@11 == curr__next_pre@73@11]
(assert (= res@94@11 curr__next_pre@73@11))
; [eval] (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre)
; [eval] new_succ_flow_pre >= 3
(push) ; 18
(push) ; 19
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_pre@123@11 3))))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 19
(set-option :timeout 10)
(assert (not (>= new_succ_flow_pre@123@11 3)))
(check-sat)
; unknown
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
; [then-branch: 104 | new_succ_flow_pre@123@11 >= 3 | live]
; [else-branch: 104 | !(new_succ_flow_pre@123@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 19
; [then-branch: 104 | new_succ_flow_pre@123@11 >= 3]
(assert (>= new_succ_flow_pre@123@11 3))
(pop) ; 19
(push) ; 19
; [else-branch: 104 | !(new_succ_flow_pre@123@11 >= 3)]
(assert (not (>= new_succ_flow_pre@123@11 3)))
(pop) ; 19
(pop) ; 18
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_pre@123@11 3)) (>= new_succ_flow_pre@123@11 3)))
(pop) ; 17
(push) ; 17
; [else-branch: 103 | res@94@11 != curr__next_pre@73@11]
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
; Joined path conditions
(pop) ; 15
(push) ; 15
; [else-branch: 98 | new_curr_flow_pre@122@11 != res@109@11 + curr__globalInflowPre@111@11 + (prev__next_pre@70@11 == curr@72@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == curr@72@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == curr@72@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (not
  (=
    new_curr_flow_pre@122@11
    (+
      (+
        (+
          (+ res@109@11 curr__globalInflowPre@111@11)
          (ite
            (= prev__next_pre@70@11 curr@72@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 curr@72@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 curr@72@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or
  (not
    (=
      new_curr_flow_pre@122@11
      (+
        (+
          (+
            (+ res@109@11 curr__globalInflowPre@111@11)
            (ite
              (= prev__next_pre@70@11 curr@72@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 curr@72@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 curr@72@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_curr_flow_pre@122@11
    (+
      (+
        (+
          (+ res@109@11 curr__globalInflowPre@111@11)
          (ite
            (= prev__next_pre@70@11 curr@72@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 curr@72@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 curr@72@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 13
(push) ; 13
; [else-branch: 91 | new_prev_flow_pre@121@11 != res@105@11 + prev__globalInflowPre@107@11 + (prev__next_pre@70@11 == prev@69@11 ? (new_prev_flow_pre@121@11 >= 3 ? 3 : new_prev_flow_pre@121@11) : 0) + (curr__next_pre@73@11 == prev@69@11 ? (new_curr_flow_pre@122@11 >= 3 ? 3 : new_curr_flow_pre@122@11) : 0) + (res@94@11 == prev@69@11 ? (new_succ_flow_pre@123@11 >= 3 ? 3 : new_succ_flow_pre@123@11) : 0)]
(assert (not
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))
  (and
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (or
      (not
        (=
          new_curr_flow_pre@122@11
          (+
            (+
              (+
                (+ res@109@11 curr__globalInflowPre@111@11)
                (ite
                  (= prev__next_pre@70@11 curr@72@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 curr@72@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 curr@72@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0))))
      (=
        new_curr_flow_pre@122@11
        (+
          (+
            (+
              (+ res@109@11 curr__globalInflowPre@111@11)
              (ite
                (= prev__next_pre@70@11 curr@72@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 curr@72@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 curr@72@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))))))
; Joined path conditions
(assert (or
  (not
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 11
(pop) ; 10
; Joined path conditions
(assert (and
  (=>
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (and
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0)))
      (or
        (not
          (=
            new_curr_flow_pre@122@11
            (+
              (+
                (+
                  (+ res@109@11 curr__globalInflowPre@111@11)
                  (ite
                    (= prev__next_pre@70@11 curr@72@11)
                    (ite
                      (>= new_prev_flow_pre@121@11 3)
                      3
                      new_prev_flow_pre@121@11)
                    0))
                (ite
                  (= curr__next_pre@73@11 curr@72@11)
                  (ite
                    (>= new_curr_flow_pre@122@11 3)
                    3
                    new_curr_flow_pre@122@11)
                  0))
              (ite
                (= res@94@11 curr@72@11)
                (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
                0))))
        (=
          new_curr_flow_pre@122@11
          (+
            (+
              (+
                (+ res@109@11 curr__globalInflowPre@111@11)
                (ite
                  (= prev__next_pre@70@11 curr@72@11)
                  (ite
                    (>= new_prev_flow_pre@121@11 3)
                    3
                    new_prev_flow_pre@121@11)
                  0))
              (ite
                (= curr__next_pre@73@11 curr@72@11)
                (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
                0))
            (ite
              (= res@94@11 curr@72@11)
              (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
              0))))))
  (or
    (not
      (=
        new_prev_flow_pre@121@11
        (+
          (+
            (+
              (+ res@105@11 prev__globalInflowPre@107@11)
              (ite
                (= prev__next_pre@70@11 prev@69@11)
                (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
                0))
            (ite
              (= curr__next_pre@73@11 prev@69@11)
              (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
              0))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
            0))))
    (=
      new_prev_flow_pre@121@11
      (+
        (+
          (+
            (+ res@105@11 prev__globalInflowPre@107@11)
            (ite
              (= prev__next_pre@70@11 prev@69@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 prev@69@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))))
(push) ; 10
(assert (not (and
  (and
    (=
      new_succ_flow_pre@123@11
      (+
        (+
          (+
            (+ res@113@11 succ__globalInflowPre@115@11)
            (ite
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11))
        (ite
          (= res@94@11 curr__next_pre@73@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (=
      new_curr_flow_pre@122@11
      (+
        (+
          (+
            (+ res@109@11 curr__globalInflowPre@111@11)
            (ite
              (= prev__next_pre@70@11 curr@72@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 curr@72@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 curr@72@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (and
  (and
    (=
      new_succ_flow_pre@123@11
      (+
        (+
          (+
            (+ res@113@11 succ__globalInflowPre@115@11)
            (ite
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11))
        (ite
          (= res@94@11 curr__next_pre@73@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0)))
    (=
      new_curr_flow_pre@122@11
      (+
        (+
          (+
            (+ res@109@11 curr__globalInflowPre@111@11)
            (ite
              (= prev__next_pre@70@11 curr@72@11)
              (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
              0))
          (ite
            (= curr__next_pre@73@11 curr@72@11)
            (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
            0))
        (ite
          (= res@94@11 curr@72@11)
          (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
          0))))
  (=
    new_prev_flow_pre@121@11
    (+
      (+
        (+
          (+ res@105@11 prev__globalInflowPre@107@11)
          (ite
            (= prev__next_pre@70@11 prev@69@11)
            (ite (>= new_prev_flow_pre@121@11 3) 3 new_prev_flow_pre@121@11)
            0))
        (ite
          (= curr__next_pre@73@11 prev@69@11)
          (ite (>= new_curr_flow_pre@122@11 3) 3 new_curr_flow_pre@122@11)
          0))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_pre@123@11 3) 3 new_succ_flow_pre@123@11)
        0)))))
(pop) ; 9
(push) ; 9
; [else-branch: 83 | !(new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11)]
(assert (not
  (and
    (and
      (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
      (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
    (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))))
(pop) ; 9
; [eval] !(new_prev_flow_pre == new_prev_flow_pre2 && (new_curr_flow_pre == new_curr_flow_pre2 && new_succ_flow_pre == new_succ_flow_pre2))
; [eval] new_prev_flow_pre == new_prev_flow_pre2 && (new_curr_flow_pre == new_curr_flow_pre2 && new_succ_flow_pre == new_succ_flow_pre2)
; [eval] new_prev_flow_pre == new_prev_flow_pre2
(push) ; 9
; [then-branch: 105 | new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11 | live]
; [else-branch: 105 | new_prev_flow_pre@121@11 != new_prev_flow_pre2@128@11 | live]
(push) ; 10
; [then-branch: 105 | new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11]
(assert (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))
; [eval] new_curr_flow_pre == new_curr_flow_pre2
(push) ; 11
; [then-branch: 106 | new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 | live]
; [else-branch: 106 | new_curr_flow_pre@122@11 != new_curr_flow_pre2@129@11 | live]
(push) ; 12
; [then-branch: 106 | new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11]
(assert (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
; [eval] new_succ_flow_pre == new_succ_flow_pre2
(pop) ; 12
(push) ; 12
; [else-branch: 106 | new_curr_flow_pre@122@11 != new_curr_flow_pre2@129@11]
(assert (not (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11)))
(pop) ; 12
(pop) ; 11
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11)))
(pop) ; 10
(push) ; 10
; [else-branch: 105 | new_prev_flow_pre@121@11 != new_prev_flow_pre2@128@11]
(assert (not (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))
(pop) ; 10
(pop) ; 9
; Joined path conditions
; Joined path conditions
(push) ; 9
(set-option :timeout 10)
(assert (not (and
  (and
    (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
    (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(set-option :timeout 10)
(assert (not (not
  (and
    (and
      (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
      (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
    (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [then-branch: 107 | !(new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11) | live]
; [else-branch: 107 | new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11 | live]
(set-option :timeout 0)
(push) ; 9
; [then-branch: 107 | !(new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11)]
(assert (not
  (and
    (and
      (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
      (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
    (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11))))
; [exec]
; new_prev_flow_pre := new_prev_flow_pre2
; [exec]
; new_curr_flow_pre := new_curr_flow_pre2
; [exec]
; new_succ_flow_pre := new_succ_flow_pre2
; [exec]
; inhale prev__flow_pre >= new_prev_flow_pre
(declare-const $t@131@11 $Snap)
(assert (= $t@131@11 $Snap.unit))
; [eval] prev__flow_pre >= new_prev_flow_pre
(assert (>= prev__flow_pre@71@11 new_prev_flow_pre2@128@11))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr__flow_pre >= new_curr_flow_pre
(declare-const $t@132@11 $Snap)
(assert (= $t@132@11 $Snap.unit))
; [eval] curr__flow_pre >= new_curr_flow_pre
(assert (>= curr__flow_pre@74@11 new_curr_flow_pre2@129@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale succ__flow_pre >= new_succ_flow_pre
(declare-const $t@133@11 $Snap)
(assert (= $t@133@11 $Snap.unit))
; [eval] succ__flow_pre >= new_succ_flow_pre
(assert (>= res@95@11 new_succ_flow_pre2@130@11))
; State saturation: after inhale
(check-sat)
; unknown
; Loop head block: Re-establish invariant
; [eval] fixpoint1 ==> new_prev_flow_pre == prev__externalInflow + prev__globalInflowPre + (prev__next_pre == prev ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == prev ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == prev ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && (new_curr_flow_pre == curr__externalInflow + curr__globalInflowPre + (prev__next_pre == curr ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == curr ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == curr ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0) && new_succ_flow_pre == succ__externalInflow + succ__globalInflowPre + (prev__next_pre == succ ? (new_prev_flow_pre >= 3 ? 3 : new_prev_flow_pre) : 0) + (curr__next_pre == succ ? (new_curr_flow_pre >= 3 ? 3 : new_curr_flow_pre) : 0) + (succ__next_pre == succ ? (new_succ_flow_pre >= 3 ? 3 : new_succ_flow_pre) : 0))
(set-option :timeout 0)
(push) ; 10
; [then-branch: 108 | fixpoint1@120@11 | dead]
; [else-branch: 108 | !(fixpoint1@120@11) | live]
(push) ; 11
; [else-branch: 108 | !(fixpoint1@120@11)]
(pop) ; 11
(pop) ; 10
; Joined path conditions
(pop) ; 9
(push) ; 9
; [else-branch: 107 | new_succ_flow_pre@123@11 == new_succ_flow_pre2@130@11 && new_curr_flow_pre@122@11 == new_curr_flow_pre2@129@11 && new_prev_flow_pre@121@11 == new_prev_flow_pre2@128@11]
(assert (and
  (and
    (= new_succ_flow_pre@123@11 new_succ_flow_pre2@130@11)
    (= new_curr_flow_pre@122@11 new_curr_flow_pre2@129@11))
  (= new_prev_flow_pre@121@11 new_prev_flow_pre2@128@11)))
(pop) ; 9
(pop) ; 8
(push) ; 8
; [else-branch: 62 | fixpoint1@120@11]
(assert fixpoint1@120@11)
(pop) ; 8
; [eval] !!fixpoint1
; [eval] !fixpoint1
(push) ; 8
(set-option :timeout 10)
(assert (not (not fixpoint1@120@11)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(set-option :timeout 10)
(assert (not fixpoint1@120@11))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [then-branch: 109 | fixpoint1@120@11 | live]
; [else-branch: 109 | !(fixpoint1@120@11) | live]
(set-option :timeout 0)
(push) ; 8
; [then-branch: 109 | fixpoint1@120@11]
(assert fixpoint1@120@11)
; [exec]
; inhale prev__flow_pre == new_prev_flow_pre
(declare-const $t@134@11 $Snap)
(assert (= $t@134@11 $Snap.unit))
; [eval] prev__flow_pre == new_prev_flow_pre
(assert (= prev__flow_pre@71@11 new_prev_flow_pre@121@11))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr__flow_pre == new_curr_flow_pre
(declare-const $t@135@11 $Snap)
(assert (= $t@135@11 $Snap.unit))
; [eval] curr__flow_pre == new_curr_flow_pre
(assert (= curr__flow_pre@74@11 new_curr_flow_pre@122@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale succ__flow_pre == new_succ_flow_pre
(declare-const $t@136@11 $Snap)
(assert (= $t@136@11 $Snap.unit))
; [eval] succ__flow_pre == new_succ_flow_pre
(assert (= res@95@11 new_succ_flow_pre@123@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; new_prev_flow_post := 0
; [exec]
; new_curr_flow_post := 0
; [exec]
; new_succ_flow_post := 0
; [exec]
; fixpoint2 := false
(declare-const new_prev_flow_post2@137@11 Int)
(declare-const new_curr_flow_post2@138@11 Int)
(declare-const new_succ_flow_post2@139@11 Int)
(declare-const fixpoint2@140@11 Bool)
(declare-const new_prev_flow_post@141@11 Int)
(declare-const new_curr_flow_post@142@11 Int)
(declare-const new_succ_flow_post@143@11 Int)
(set-option :timeout 0)
(push) ; 9
; Loop head block: Check well-definedness of invariant
(declare-const $t@144@11 $Snap)
(assert (= $t@144@11 $Snap.unit))
; [eval] fixpoint2 ==> new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
(push) ; 10
(push) ; 11
(set-option :timeout 10)
(assert (not (not fixpoint2@140@11)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(set-option :timeout 10)
(assert (not fixpoint2@140@11))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [then-branch: 110 | fixpoint2@140@11 | live]
; [else-branch: 110 | !(fixpoint2@140@11) | live]
(set-option :timeout 0)
(push) ; 11
; [then-branch: 110 | fixpoint2@140@11]
(assert fixpoint2@140@11)
; [eval] new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
; [eval] new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost
; [eval] (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 prev@69@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 111 | prev__next_pre@70@11 == prev@69@11 | dead]
; [else-branch: 111 | prev__next_pre@70@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 111 | prev__next_pre@70@11 != prev@69@11]
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= prev__next_pre@70@11 prev@69@11)))
; [eval] (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 112 | True | live]
; [else-branch: 112 | False | dead]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 112 | True]
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_post@142@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_curr_flow_post@142@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 113 | new_curr_flow_post@142@11 >= 3 | live]
; [else-branch: 113 | !(new_curr_flow_post@142@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 113 | new_curr_flow_post@142@11 >= 3]
(assert (>= new_curr_flow_post@142@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 113 | !(new_curr_flow_post@142@11 >= 3)]
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3)))
; [eval] (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 114 | res@94@11 == prev@69@11 | live]
; [else-branch: 114 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 114 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post)
; [eval] new_succ_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_post@143@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_succ_flow_post@143@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 115 | new_succ_flow_post@143@11 >= 3 | live]
; [else-branch: 115 | !(new_succ_flow_post@143@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 115 | new_succ_flow_post@143@11 >= 3]
(assert (>= new_succ_flow_post@143@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 115 | !(new_succ_flow_post@143@11 >= 3)]
(assert (not (>= new_succ_flow_post@143@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_post@143@11 3)) (>= new_succ_flow_post@143@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 114 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= res@94@11 prev@69@11)
  (and
    (= res@94@11 prev@69@11)
    (or (not (>= new_succ_flow_post@143@11 3)) (>= new_succ_flow_post@143@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11)))
(push) ; 12
; [then-branch: 116 | new_prev_flow_post@141@11 == res@105@11 + prev__globalInflowPost@108@11 + (new_curr_flow_post@142@11 >= 3 ? 3 : new_curr_flow_post@142@11) + (res@94@11 == prev@69@11 ? (new_succ_flow_post@143@11 >= 3 ? 3 : new_succ_flow_post@143@11) : 0) | live]
; [else-branch: 116 | new_prev_flow_post@141@11 != res@105@11 + prev__globalInflowPost@108@11 + (new_curr_flow_post@142@11 >= 3 ? 3 : new_curr_flow_post@142@11) + (res@94@11 == prev@69@11 ? (new_succ_flow_post@143@11 >= 3 ? 3 : new_succ_flow_post@143@11) : 0) | live]
(push) ; 13
; [then-branch: 116 | new_prev_flow_post@141@11 == res@105@11 + prev__globalInflowPost@108@11 + (new_curr_flow_post@142@11 >= 3 ? 3 : new_curr_flow_post@142@11) + (res@94@11 == prev@69@11 ? (new_succ_flow_post@143@11 >= 3 ? 3 : new_succ_flow_post@143@11) : 0)]
(assert (=
  new_prev_flow_post@141@11
  (+
    (+
      (+ res@105@11 prev__globalInflowPost@108@11)
      (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
    (ite
      (= res@94@11 prev@69@11)
      (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
      0))))
; [eval] new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost
; [eval] (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 117 | prev__next_pre@70@11 == curr@72@11 | dead]
; [else-branch: 117 | prev__next_pre@70@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 117 | prev__next_pre@70@11 != curr@72@11]
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (= prev__next_pre@70@11 curr@72@11)))
; [eval] (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= prev@69@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 118 | prev@69@11 == curr@72@11 | dead]
; [else-branch: 118 | prev@69@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 118 | prev@69@11 != curr@72@11]
(assert (not (= prev@69@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (= prev@69@11 curr@72@11)))
; [eval] (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == curr
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 119 | res@94@11 == curr@72@11 | dead]
; [else-branch: 119 | res@94@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 119 | res@94@11 != curr@72@11]
(assert (not (= res@94@11 curr@72@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (= res@94@11 curr@72@11)))
(push) ; 14
; [then-branch: 120 | new_curr_flow_post@142@11 == res@109@11 + curr__globalInflowPost@112@11 | live]
; [else-branch: 120 | new_curr_flow_post@142@11 != res@109@11 + curr__globalInflowPost@112@11 | live]
(push) ; 15
; [then-branch: 120 | new_curr_flow_post@142@11 == res@109@11 + curr__globalInflowPost@112@11]
(assert (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
; [eval] new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost
; [eval] (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 121 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 121 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 121 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post)
; [eval] new_prev_flow_post >= 3
(push) ; 18
(push) ; 19
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_post@141@11 3))))
(check-sat)
; unsat
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
; [then-branch: 122 | new_prev_flow_post@141@11 >= 3 | dead]
; [else-branch: 122 | !(new_prev_flow_post@141@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 19
; [else-branch: 122 | !(new_prev_flow_post@141@11 >= 3)]
(assert (not (>= new_prev_flow_post@141@11 3)))
(pop) ; 19
(pop) ; 18
; Joined path conditions
(assert (not (>= new_prev_flow_post@141@11 3)))
(pop) ; 17
(push) ; 17
; [else-branch: 121 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr__next_pre@73@11)
  (and
    (= prev__next_pre@70@11 curr__next_pre@73@11)
    (not (>= new_prev_flow_post@141@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr__next_pre@73@11))
  (= prev__next_pre@70@11 curr__next_pre@73@11)))
; [eval] (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (= prev@69@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 17
(set-option :timeout 10)
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 123 | prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 123 | prev@69@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 17
; [then-branch: 123 | prev@69@11 == curr__next_pre@73@11]
(assert (= prev@69@11 curr__next_pre@73@11))
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 18
(push) ; 19
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_post@142@11 3))))
(check-sat)
; unsat
(pop) ; 19
; 0.00s
; (get-info :all-statistics)
; [then-branch: 124 | new_curr_flow_post@142@11 >= 3 | dead]
; [else-branch: 124 | !(new_curr_flow_post@142@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 19
; [else-branch: 124 | !(new_curr_flow_post@142@11 >= 3)]
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 19
(pop) ; 18
; Joined path conditions
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 17
(push) ; 17
; [else-branch: 123 | prev@69@11 != curr__next_pre@73@11]
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
(assert (=>
  (= prev@69@11 curr__next_pre@73@11)
  (and
    (= prev@69@11 curr__next_pre@73@11)
    (not (>= new_curr_flow_post@142@11 3)))))
; Joined path conditions
; [eval] (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == succ
(push) ; 16
(push) ; 17
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr__next_pre@73@11))))
(check-sat)
; unsat
(pop) ; 17
; 0.00s
; (get-info :all-statistics)
; [then-branch: 125 | res@94@11 == curr__next_pre@73@11 | dead]
; [else-branch: 125 | res@94@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 17
; [else-branch: 125 | res@94@11 != curr__next_pre@73@11]
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 17
(pop) ; 16
; Joined path conditions
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 15
(push) ; 15
; [else-branch: 120 | new_curr_flow_post@142@11 != res@109@11 + curr__globalInflowPost@112@11]
(assert (not (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (=>
  (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
  (and
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
    (=>
      (= prev__next_pre@70@11 curr__next_pre@73@11)
      (and
        (= prev__next_pre@70@11 curr__next_pre@73@11)
        (not (>= new_prev_flow_post@141@11 3))))
    (or
      (not (= prev__next_pre@70@11 curr__next_pre@73@11))
      (= prev__next_pre@70@11 curr__next_pre@73@11))
    (=>
      (= prev@69@11 curr__next_pre@73@11)
      (and
        (= prev@69@11 curr__next_pre@73@11)
        (not (>= new_curr_flow_post@142@11 3))))
    (not (= res@94@11 curr__next_pre@73@11)))))
; Joined path conditions
(assert (or
  (not
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
  (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))
(pop) ; 13
(push) ; 13
; [else-branch: 116 | new_prev_flow_post@141@11 != res@105@11 + prev__globalInflowPost@108@11 + (new_curr_flow_post@142@11 >= 3 ? 3 : new_curr_flow_post@142@11) + (res@94@11 == prev@69@11 ? (new_succ_flow_post@143@11 >= 3 ? 3 : new_succ_flow_post@143@11) : 0)]
(assert (not
  (=
    new_prev_flow_post@141@11
    (+
      (+
        (+ res@105@11 prev__globalInflowPost@108@11)
        (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
        0)))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (=
    new_prev_flow_post@141@11
    (+
      (+
        (+ res@105@11 prev__globalInflowPost@108@11)
        (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
        0)))
  (and
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
          0)))
    (not (= prev__next_pre@70@11 curr@72@11))
    (not (= prev@69@11 curr@72@11))
    (not (= res@94@11 curr@72@11))
    (=>
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
      (and
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11))
        (=>
          (= prev__next_pre@70@11 curr__next_pre@73@11)
          (and
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            (not (>= new_prev_flow_post@141@11 3))))
        (or
          (not (= prev__next_pre@70@11 curr__next_pre@73@11))
          (= prev__next_pre@70@11 curr__next_pre@73@11))
        (=>
          (= prev@69@11 curr__next_pre@73@11)
          (and
            (= prev@69@11 curr__next_pre@73@11)
            (not (>= new_curr_flow_post@142@11 3))))
        (not (= res@94@11 curr__next_pre@73@11))))
    (or
      (not
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11)))
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))))
; Joined path conditions
(assert (or
  (not
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
          0))))
  (=
    new_prev_flow_post@141@11
    (+
      (+
        (+ res@105@11 prev__globalInflowPost@108@11)
        (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
      (ite
        (= res@94@11 prev@69@11)
        (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
        0)))))
(pop) ; 11
(push) ; 11
; [else-branch: 110 | !(fixpoint2@140@11)]
(assert (not fixpoint2@140@11))
(pop) ; 11
(pop) ; 10
; Joined path conditions
(assert (=>
  fixpoint2@140@11
  (and
    fixpoint2@140@11
    (not (= prev__next_pre@70@11 prev@69@11))
    (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3))
    (=>
      (= res@94@11 prev@69@11)
      (and
        (= res@94@11 prev@69@11)
        (or
          (not (>= new_succ_flow_post@143@11 3))
          (>= new_succ_flow_post@143@11 3))))
    (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11))
    (=>
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
            0)))
      (and
        (=
          new_prev_flow_post@141@11
          (+
            (+
              (+ res@105@11 prev__globalInflowPost@108@11)
              (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
              0)))
        (not (= prev__next_pre@70@11 curr@72@11))
        (not (= prev@69@11 curr@72@11))
        (not (= res@94@11 curr@72@11))
        (=>
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11))
          (and
            (=
              new_curr_flow_post@142@11
              (+ res@109@11 curr__globalInflowPost@112@11))
            (=>
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (and
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (not (>= new_prev_flow_post@141@11 3))))
            (or
              (not (= prev__next_pre@70@11 curr__next_pre@73@11))
              (= prev__next_pre@70@11 curr__next_pre@73@11))
            (=>
              (= prev@69@11 curr__next_pre@73@11)
              (and
                (= prev@69@11 curr__next_pre@73@11)
                (not (>= new_curr_flow_post@142@11 3))))
            (not (= res@94@11 curr__next_pre@73@11))))
        (or
          (not
            (=
              new_curr_flow_post@142@11
              (+ res@109@11 curr__globalInflowPost@112@11)))
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11)))))
    (or
      (not
        (=
          new_prev_flow_post@141@11
          (+
            (+
              (+ res@105@11 prev__globalInflowPost@108@11)
              (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
              0))))
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
            0)))))))
; Joined path conditions
(assert (or (not fixpoint2@140@11) fixpoint2@140@11))
(assert (=>
  fixpoint2@140@11
  (and
    (and
      (=
        new_succ_flow_post@143@11
        (+
          (+
            (+ res@113@11 succ__globalInflowPost@116@11)
            (ite
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              new_prev_flow_post@141@11
              0))
          (ite (= prev@69@11 curr__next_pre@73@11) new_curr_flow_post@142@11 0)))
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
          0))))))
; Loop head block: Check well-definedness of edge conditions
(push) ; 10
; [eval] !fixpoint2
(pop) ; 10
(push) ; 10
; [eval] !!fixpoint2
; [eval] !fixpoint2
(pop) ; 10
(pop) ; 9
(push) ; 9
; Loop head block: Establish invariant
; [eval] fixpoint2 ==> new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
(push) ; 10
; [then-branch: 126 | False | dead]
; [else-branch: 126 | True | live]
(push) ; 11
; [else-branch: 126 | True]
(pop) ; 11
(pop) ; 10
; Joined path conditions
; Loop head block: Execute statements of loop head block (in invariant state)
(push) ; 10
(assert (= $t@144@11 $Snap.unit))
(assert (=>
  fixpoint2@140@11
  (and
    fixpoint2@140@11
    (not (= prev__next_pre@70@11 prev@69@11))
    (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3))
    (=>
      (= res@94@11 prev@69@11)
      (and
        (= res@94@11 prev@69@11)
        (or
          (not (>= new_succ_flow_post@143@11 3))
          (>= new_succ_flow_post@143@11 3))))
    (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11))
    (=>
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
            0)))
      (and
        (=
          new_prev_flow_post@141@11
          (+
            (+
              (+ res@105@11 prev__globalInflowPost@108@11)
              (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
              0)))
        (not (= prev__next_pre@70@11 curr@72@11))
        (not (= prev@69@11 curr@72@11))
        (not (= res@94@11 curr@72@11))
        (=>
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11))
          (and
            (=
              new_curr_flow_post@142@11
              (+ res@109@11 curr__globalInflowPost@112@11))
            (=>
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (and
                (= prev__next_pre@70@11 curr__next_pre@73@11)
                (not (>= new_prev_flow_post@141@11 3))))
            (or
              (not (= prev__next_pre@70@11 curr__next_pre@73@11))
              (= prev__next_pre@70@11 curr__next_pre@73@11))
            (=>
              (= prev@69@11 curr__next_pre@73@11)
              (and
                (= prev@69@11 curr__next_pre@73@11)
                (not (>= new_curr_flow_post@142@11 3))))
            (not (= res@94@11 curr__next_pre@73@11))))
        (or
          (not
            (=
              new_curr_flow_post@142@11
              (+ res@109@11 curr__globalInflowPost@112@11)))
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11)))))
    (or
      (not
        (=
          new_prev_flow_post@141@11
          (+
            (+
              (+ res@105@11 prev__globalInflowPost@108@11)
              (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
            (ite
              (= res@94@11 prev@69@11)
              (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
              0))))
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
          (ite
            (= res@94@11 prev@69@11)
            (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
            0)))))))
(assert (or (not fixpoint2@140@11) fixpoint2@140@11))
(assert (=>
  fixpoint2@140@11
  (and
    (and
      (=
        new_succ_flow_post@143@11
        (+
          (+
            (+ res@113@11 succ__globalInflowPost@116@11)
            (ite
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              new_prev_flow_post@141@11
              0))
          (ite (= prev@69@11 curr__next_pre@73@11) new_curr_flow_post@142@11 0)))
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
        (ite
          (= res@94@11 prev@69@11)
          (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
          0))))))
; State saturation: after contract
(set-option :timeout 50)
(check-sat)
; unknown
(set-option :timeout 10)
(check-sat)
; unknown
; Loop head block: Follow loop-internal edges
; [eval] !fixpoint2
(set-option :timeout 0)
(push) ; 11
(set-option :timeout 10)
(assert (not fixpoint2@140@11))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(set-option :timeout 10)
(assert (not (not fixpoint2@140@11)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [then-branch: 127 | !(fixpoint2@140@11) | live]
; [else-branch: 127 | fixpoint2@140@11 | live]
(set-option :timeout 0)
(push) ; 11
; [then-branch: 127 | !(fixpoint2@140@11)]
(assert (not fixpoint2@140@11))
; [exec]
; var new_prev_flow_post2: Int
(declare-const new_prev_flow_post2@145@11 Int)
; [exec]
; var new_curr_flow_post2: Int
(declare-const new_curr_flow_post2@146@11 Int)
; [exec]
; var new_succ_flow_post2: Int
(declare-const new_succ_flow_post2@147@11 Int)
; [exec]
; new_prev_flow_post2 := prev__externalInflow + prev__globalInflowPost +
;   (prev__next_post == prev ?
;     (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) :
;     0) +
;   (curr__next_post == prev ?
;     (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) :
;     0) +
;   (succ__next_post == prev ?
;     (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) :
;     0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost
; [eval] (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 prev@69@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 128 | prev__next_pre@70@11 == prev@69@11 | dead]
; [else-branch: 128 | prev__next_pre@70@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 128 | prev__next_pre@70@11 != prev@69@11]
(assert (not (= prev__next_pre@70@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= prev__next_pre@70@11 prev@69@11)))
; [eval] (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 129 | True | live]
; [else-branch: 129 | False | dead]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 129 | True]
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_post@142@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_curr_flow_post@142@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 130 | new_curr_flow_post@142@11 >= 3 | live]
; [else-branch: 130 | !(new_curr_flow_post@142@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 130 | new_curr_flow_post@142@11 >= 3]
(assert (>= new_curr_flow_post@142@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 130 | !(new_curr_flow_post@142@11 >= 3)]
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (or (not (>= new_curr_flow_post@142@11 3)) (>= new_curr_flow_post@142@11 3)))
; [eval] (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == prev
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 131 | res@94@11 == prev@69@11 | live]
; [else-branch: 131 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 131 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post)
; [eval] new_succ_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_post@143@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_succ_flow_post@143@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 132 | new_succ_flow_post@143@11 >= 3 | live]
; [else-branch: 132 | !(new_succ_flow_post@143@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 132 | new_succ_flow_post@143@11 >= 3]
(assert (>= new_succ_flow_post@143@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 132 | !(new_succ_flow_post@143@11 >= 3)]
(assert (not (>= new_succ_flow_post@143@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_succ_flow_post@143@11 3)) (>= new_succ_flow_post@143@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 131 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= res@94@11 prev@69@11)
  (and
    (= res@94@11 prev@69@11)
    (or (not (>= new_succ_flow_post@143@11 3)) (>= new_succ_flow_post@143@11 3)))))
; Joined path conditions
(assert (or (not (= res@94@11 prev@69@11)) (= res@94@11 prev@69@11)))
(declare-const new_prev_flow_post2@148@11 Int)
(assert (=
  new_prev_flow_post2@148@11
  (+
    (+
      (+ res@105@11 prev__globalInflowPost@108@11)
      (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11))
    (ite
      (= res@94@11 prev@69@11)
      (ite (>= new_succ_flow_post@143@11 3) 3 new_succ_flow_post@143@11)
      0))))
; [exec]
; new_curr_flow_post2 := curr__externalInflow + curr__globalInflowPost +
;   (prev__next_post == curr ?
;     (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) :
;     0) +
;   (curr__next_post == curr ?
;     (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) :
;     0) +
;   (succ__next_post == curr ?
;     (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) :
;     0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost
; [eval] (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == curr
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 133 | prev__next_pre@70@11 == curr@72@11 | dead]
; [else-branch: 133 | prev__next_pre@70@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 133 | prev__next_pre@70@11 != curr@72@11]
(assert (not (= prev__next_pre@70@11 curr@72@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= prev__next_pre@70@11 curr@72@11)))
; [eval] (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == curr
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev@69@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 134 | prev@69@11 == curr@72@11 | dead]
; [else-branch: 134 | prev@69@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 134 | prev@69@11 != curr@72@11]
(assert (not (= prev@69@11 curr@72@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= prev@69@11 curr@72@11)))
; [eval] (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == curr
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr@72@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 135 | res@94@11 == curr@72@11 | dead]
; [else-branch: 135 | res@94@11 != curr@72@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 135 | res@94@11 != curr@72@11]
(assert (not (= res@94@11 curr@72@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= res@94@11 curr@72@11)))
(declare-const new_curr_flow_post2@149@11 Int)
(assert (= new_curr_flow_post2@149@11 (+ res@109@11 curr__globalInflowPost@112@11)))
; [exec]
; new_succ_flow_post2 := succ__externalInflow + succ__globalInflowPost +
;   (prev__next_post == succ ?
;     (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) :
;     0) +
;   (curr__next_post == succ ?
;     (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) :
;     0) +
;   (succ__next_post == succ ?
;     (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) :
;     0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost
; [eval] (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == succ
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 136 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 136 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 136 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post)
; [eval] new_prev_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_post@141@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_prev_flow_post@141@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 137 | new_prev_flow_post@141@11 >= 3 | live]
; [else-branch: 137 | !(new_prev_flow_post@141@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 137 | new_prev_flow_post@141@11 >= 3]
(assert (>= new_prev_flow_post@141@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 137 | !(new_prev_flow_post@141@11 >= 3)]
(assert (not (>= new_prev_flow_post@141@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or (not (>= new_prev_flow_post@141@11 3)) (>= new_prev_flow_post@141@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 136 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr__next_pre@73@11)
  (and
    (= prev__next_pre@70@11 curr__next_pre@73@11)
    (or (not (>= new_prev_flow_post@141@11 3)) (>= new_prev_flow_post@141@11 3)))))
; Joined path conditions
(assert (or
  (not (= prev__next_pre@70@11 curr__next_pre@73@11))
  (= prev__next_pre@70@11 curr__next_pre@73@11)))
; [eval] (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == succ
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev@69@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 138 | prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 138 | prev@69@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 138 | prev@69@11 == curr__next_pre@73@11]
(assert (= prev@69@11 curr__next_pre@73@11))
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_post@142@11 3))))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 15
(set-option :timeout 10)
(assert (not (>= new_curr_flow_post@142@11 3)))
(check-sat)
; unknown
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 139 | new_curr_flow_post@142@11 >= 3 | live]
; [else-branch: 139 | !(new_curr_flow_post@142@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [then-branch: 139 | new_curr_flow_post@142@11 >= 3]
(assert (>= new_curr_flow_post@142@11 3))
(pop) ; 15
(push) ; 15
; [else-branch: 139 | !(new_curr_flow_post@142@11 >= 3)]
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(pop) ; 13
(push) ; 13
; [else-branch: 138 | prev@69@11 != curr__next_pre@73@11]
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [eval] (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == succ
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= res@94@11 curr__next_pre@73@11))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 140 | res@94@11 == curr__next_pre@73@11 | dead]
; [else-branch: 140 | res@94@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 13
; [else-branch: 140 | res@94@11 != curr__next_pre@73@11]
(assert (not (= res@94@11 curr__next_pre@73@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (not (= res@94@11 curr__next_pre@73@11)))
(declare-const new_succ_flow_post2@150@11 Int)
(assert (=
  new_succ_flow_post2@150@11
  (+
    (+
      (+ res@113@11 succ__globalInflowPost@116@11)
      (ite
        (= prev__next_pre@70@11 curr__next_pre@73@11)
        (ite (>= new_prev_flow_post@141@11 3) 3 new_prev_flow_post@141@11)
        0))
    (ite
      (= prev@69@11 curr__next_pre@73@11)
      (ite (>= new_curr_flow_post@142@11 3) 3 new_curr_flow_post@142@11)
      0))))
; [eval] new_prev_flow_post == new_prev_flow_post2 && (new_curr_flow_post == new_curr_flow_post2 && new_succ_flow_post == new_succ_flow_post2)
; [eval] new_prev_flow_post == new_prev_flow_post2
(push) ; 12
; [then-branch: 141 | new_prev_flow_post@141@11 == new_prev_flow_post2@148@11 | live]
; [else-branch: 141 | new_prev_flow_post@141@11 != new_prev_flow_post2@148@11 | live]
(push) ; 13
; [then-branch: 141 | new_prev_flow_post@141@11 == new_prev_flow_post2@148@11]
(assert (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))
; [eval] new_curr_flow_post == new_curr_flow_post2
(push) ; 14
; [then-branch: 142 | new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 | live]
; [else-branch: 142 | new_curr_flow_post@142@11 != new_curr_flow_post2@149@11 | live]
(push) ; 15
; [then-branch: 142 | new_curr_flow_post@142@11 == new_curr_flow_post2@149@11]
(assert (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
; [eval] new_succ_flow_post == new_succ_flow_post2
(pop) ; 15
(push) ; 15
; [else-branch: 142 | new_curr_flow_post@142@11 != new_curr_flow_post2@149@11]
(assert (not (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11)))
(pop) ; 13
(push) ; 13
; [else-branch: 141 | new_prev_flow_post@141@11 != new_prev_flow_post2@148@11]
(assert (not (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)
  (and
    (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)
    (or
      (not (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
      (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11)))))
; Joined path conditions
(assert (or
  (not (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))
(push) ; 12
(set-option :timeout 10)
(assert (not (not
  (and
    (and
      (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
      (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
    (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (and
  (and
    (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
    (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 143 | new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11 | live]
; [else-branch: 143 | !(new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11) | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 143 | new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11]
(assert (and
  (and
    (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
    (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))
; [exec]
; fixpoint2 := true
; Loop head block: Re-establish invariant
; [eval] fixpoint2 ==> new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
(push) ; 13
(push) ; 14
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
; [then-branch: 144 | True | live]
; [else-branch: 144 | False | dead]
(set-option :timeout 0)
(push) ; 14
; [then-branch: 144 | True]
; [eval] new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
; [eval] new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__externalInflow + prev__globalInflowPost
; [eval] (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == prev
(push) ; 15
; [then-branch: 145 | prev__next_pre@70@11 == prev@69@11 | dead]
; [else-branch: 145 | prev__next_pre@70@11 != prev@69@11 | live]
(push) ; 16
; [else-branch: 145 | prev__next_pre@70@11 != prev@69@11]
(pop) ; 16
(pop) ; 15
; Joined path conditions
; [eval] (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == prev
(push) ; 15
(push) ; 16
(set-option :timeout 10)
(assert (not false))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
; [then-branch: 146 | True | live]
; [else-branch: 146 | False | dead]
(set-option :timeout 0)
(push) ; 16
; [then-branch: 146 | True]
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 17
(push) ; 18
(set-option :timeout 10)
(assert (not (not (>= new_curr_flow_post@142@11 3))))
(check-sat)
; unsat
(pop) ; 18
; 0.00s
; (get-info :all-statistics)
; [then-branch: 147 | new_curr_flow_post@142@11 >= 3 | dead]
; [else-branch: 147 | !(new_curr_flow_post@142@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 18
; [else-branch: 147 | !(new_curr_flow_post@142@11 >= 3)]
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 18
(pop) ; 17
; Joined path conditions
(assert (not (>= new_curr_flow_post@142@11 3)))
(pop) ; 16
(pop) ; 15
; Joined path conditions
(assert (not (>= new_curr_flow_post@142@11 3)))
; [eval] (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == prev
(push) ; 15
(push) ; 16
(set-option :timeout 10)
(assert (not (not (= res@94@11 prev@69@11))))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 16
(set-option :timeout 10)
(assert (not (= res@94@11 prev@69@11)))
(check-sat)
; unknown
(pop) ; 16
; 0.00s
; (get-info :all-statistics)
; [then-branch: 148 | res@94@11 == prev@69@11 | live]
; [else-branch: 148 | res@94@11 != prev@69@11 | live]
(set-option :timeout 0)
(push) ; 16
; [then-branch: 148 | res@94@11 == prev@69@11]
(assert (= res@94@11 prev@69@11))
; [eval] (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post)
; [eval] new_succ_flow_post >= 3
(push) ; 17
(push) ; 18
(set-option :timeout 10)
(assert (not (not (>= new_succ_flow_post@143@11 3))))
(check-sat)
; unsat
(pop) ; 18
; 0.00s
; (get-info :all-statistics)
; [then-branch: 149 | new_succ_flow_post@143@11 >= 3 | dead]
; [else-branch: 149 | !(new_succ_flow_post@143@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 18
; [else-branch: 149 | !(new_succ_flow_post@143@11 >= 3)]
(assert (not (>= new_succ_flow_post@143@11 3)))
(pop) ; 18
(pop) ; 17
; Joined path conditions
(assert (not (>= new_succ_flow_post@143@11 3)))
(pop) ; 16
(push) ; 16
; [else-branch: 148 | res@94@11 != prev@69@11]
(assert (not (= res@94@11 prev@69@11)))
(pop) ; 16
(pop) ; 15
; Joined path conditions
(assert (=>
  (= res@94@11 prev@69@11)
  (and (= res@94@11 prev@69@11) (not (>= new_succ_flow_post@143@11 3)))))
; Joined path conditions
(push) ; 15
; [then-branch: 150 | new_prev_flow_post@141@11 == res@105@11 + prev__globalInflowPost@108@11 + new_curr_flow_post@142@11 + (res@94@11 == prev@69@11 ? new_succ_flow_post@143@11 : 0) | live]
; [else-branch: 150 | new_prev_flow_post@141@11 != res@105@11 + prev__globalInflowPost@108@11 + new_curr_flow_post@142@11 + (res@94@11 == prev@69@11 ? new_succ_flow_post@143@11 : 0) | live]
(push) ; 16
; [then-branch: 150 | new_prev_flow_post@141@11 == res@105@11 + prev__globalInflowPost@108@11 + new_curr_flow_post@142@11 + (res@94@11 == prev@69@11 ? new_succ_flow_post@143@11 : 0)]
(assert (=
  new_prev_flow_post@141@11
  (+
    (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
    (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0))))
; [eval] new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] curr__externalInflow + curr__globalInflowPost
; [eval] (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == curr
(push) ; 17
; [then-branch: 151 | prev__next_pre@70@11 == curr@72@11 | dead]
; [else-branch: 151 | prev__next_pre@70@11 != curr@72@11 | live]
(push) ; 18
; [else-branch: 151 | prev__next_pre@70@11 != curr@72@11]
(pop) ; 18
(pop) ; 17
; Joined path conditions
; [eval] (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == curr
(push) ; 17
; [then-branch: 152 | prev@69@11 == curr@72@11 | dead]
; [else-branch: 152 | prev@69@11 != curr@72@11 | live]
(push) ; 18
; [else-branch: 152 | prev@69@11 != curr@72@11]
(pop) ; 18
(pop) ; 17
; Joined path conditions
; [eval] (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == curr
(push) ; 17
; [then-branch: 153 | res@94@11 == curr@72@11 | dead]
; [else-branch: 153 | res@94@11 != curr@72@11 | live]
(push) ; 18
; [else-branch: 153 | res@94@11 != curr@72@11]
(pop) ; 18
(pop) ; 17
; Joined path conditions
(push) ; 17
; [then-branch: 154 | new_curr_flow_post@142@11 == res@109@11 + curr__globalInflowPost@112@11 | live]
; [else-branch: 154 | new_curr_flow_post@142@11 != res@109@11 + curr__globalInflowPost@112@11 | live]
(push) ; 18
; [then-branch: 154 | new_curr_flow_post@142@11 == res@109@11 + curr__globalInflowPost@112@11]
(assert (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
; [eval] new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] succ__externalInflow + succ__globalInflowPost
; [eval] (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0)
; [eval] prev__next_post == succ
(push) ; 19
(push) ; 20
(set-option :timeout 10)
(assert (not (not (= prev__next_pre@70@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 20
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 20
(set-option :timeout 10)
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 20
; 0.00s
; (get-info :all-statistics)
; [then-branch: 155 | prev__next_pre@70@11 == curr__next_pre@73@11 | live]
; [else-branch: 155 | prev__next_pre@70@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 20
; [then-branch: 155 | prev__next_pre@70@11 == curr__next_pre@73@11]
(assert (= prev__next_pre@70@11 curr__next_pre@73@11))
; [eval] (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post)
; [eval] new_prev_flow_post >= 3
(push) ; 21
(push) ; 22
(set-option :timeout 10)
(assert (not (not (>= new_prev_flow_post@141@11 3))))
(check-sat)
; unsat
(pop) ; 22
; 0.00s
; (get-info :all-statistics)
; [then-branch: 156 | new_prev_flow_post@141@11 >= 3 | dead]
; [else-branch: 156 | !(new_prev_flow_post@141@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 22
; [else-branch: 156 | !(new_prev_flow_post@141@11 >= 3)]
(assert (not (>= new_prev_flow_post@141@11 3)))
(pop) ; 22
(pop) ; 21
; Joined path conditions
(assert (not (>= new_prev_flow_post@141@11 3)))
(pop) ; 20
(push) ; 20
; [else-branch: 155 | prev__next_pre@70@11 != curr__next_pre@73@11]
(assert (not (= prev__next_pre@70@11 curr__next_pre@73@11)))
(pop) ; 20
(pop) ; 19
; Joined path conditions
(assert (=>
  (= prev__next_pre@70@11 curr__next_pre@73@11)
  (and
    (= prev__next_pre@70@11 curr__next_pre@73@11)
    (not (>= new_prev_flow_post@141@11 3)))))
; Joined path conditions
; [eval] (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0)
; [eval] curr__next_post == succ
(push) ; 19
(push) ; 20
(set-option :timeout 10)
(assert (not (not (= prev@69@11 curr__next_pre@73@11))))
(check-sat)
; unknown
(pop) ; 20
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 20
(set-option :timeout 10)
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(check-sat)
; unknown
(pop) ; 20
; 0.00s
; (get-info :all-statistics)
; [then-branch: 157 | prev@69@11 == curr__next_pre@73@11 | live]
; [else-branch: 157 | prev@69@11 != curr__next_pre@73@11 | live]
(set-option :timeout 0)
(push) ; 20
; [then-branch: 157 | prev@69@11 == curr__next_pre@73@11]
(assert (= prev@69@11 curr__next_pre@73@11))
; [eval] (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post)
; [eval] new_curr_flow_post >= 3
(push) ; 21
; [then-branch: 158 | new_curr_flow_post@142@11 >= 3 | dead]
; [else-branch: 158 | !(new_curr_flow_post@142@11 >= 3) | live]
(push) ; 22
; [else-branch: 158 | !(new_curr_flow_post@142@11 >= 3)]
(pop) ; 22
(pop) ; 21
; Joined path conditions
(pop) ; 20
(push) ; 20
; [else-branch: 157 | prev@69@11 != curr__next_pre@73@11]
(assert (not (= prev@69@11 curr__next_pre@73@11)))
(pop) ; 20
(pop) ; 19
; Joined path conditions
; Joined path conditions
; [eval] (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0)
; [eval] succ__next_post == succ
(push) ; 19
; [then-branch: 159 | res@94@11 == curr__next_pre@73@11 | dead]
; [else-branch: 159 | res@94@11 != curr__next_pre@73@11 | live]
(push) ; 20
; [else-branch: 159 | res@94@11 != curr__next_pre@73@11]
(pop) ; 20
(pop) ; 19
; Joined path conditions
(pop) ; 18
(push) ; 18
; [else-branch: 154 | new_curr_flow_post@142@11 != res@109@11 + curr__globalInflowPost@112@11]
(assert (not (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))
(pop) ; 18
(pop) ; 17
; Joined path conditions
(assert (=>
  (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
  (and
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
    (=>
      (= prev__next_pre@70@11 curr__next_pre@73@11)
      (and
        (= prev__next_pre@70@11 curr__next_pre@73@11)
        (not (>= new_prev_flow_post@141@11 3)))))))
; Joined path conditions
(assert (or
  (not
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
  (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))
(pop) ; 16
(push) ; 16
; [else-branch: 150 | new_prev_flow_post@141@11 != res@105@11 + prev__globalInflowPost@108@11 + new_curr_flow_post@142@11 + (res@94@11 == prev@69@11 ? new_succ_flow_post@143@11 : 0)]
(assert (not
  (=
    new_prev_flow_post@141@11
    (+
      (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
      (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))))
(pop) ; 16
(pop) ; 15
; Joined path conditions
(assert (=>
  (=
    new_prev_flow_post@141@11
    (+
      (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
      (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))
  (and
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          new_curr_flow_post@142@11)
        (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))
    (=>
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))
      (and
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11))
        (=>
          (= prev__next_pre@70@11 curr__next_pre@73@11)
          (and
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            (not (>= new_prev_flow_post@141@11 3))))))
    (or
      (not
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11)))
      (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11))))))
; Joined path conditions
(assert (or
  (not
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          new_curr_flow_post@142@11)
        (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0))))
  (=
    new_prev_flow_post@141@11
    (+
      (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
      (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))))
(pop) ; 14
(pop) ; 13
; Joined path conditions
(assert (and
  (not (>= new_curr_flow_post@142@11 3))
  (=>
    (= res@94@11 prev@69@11)
    (and (= res@94@11 prev@69@11) (not (>= new_succ_flow_post@143@11 3))))
  (=>
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          new_curr_flow_post@142@11)
        (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))
    (and
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            new_curr_flow_post@142@11)
          (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))
      (=>
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11))
        (and
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11))
          (=>
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            (and
              (= prev__next_pre@70@11 curr__next_pre@73@11)
              (not (>= new_prev_flow_post@141@11 3))))))
      (or
        (not
          (=
            new_curr_flow_post@142@11
            (+ res@109@11 curr__globalInflowPost@112@11)))
        (=
          new_curr_flow_post@142@11
          (+ res@109@11 curr__globalInflowPost@112@11)))))
  (or
    (not
      (=
        new_prev_flow_post@141@11
        (+
          (+
            (+ res@105@11 prev__globalInflowPost@108@11)
            new_curr_flow_post@142@11)
          (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0))))
    (=
      new_prev_flow_post@141@11
      (+
        (+
          (+ res@105@11 prev__globalInflowPost@108@11)
          new_curr_flow_post@142@11)
        (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0))))))
(push) ; 13
(assert (not (and
  (and
    (=
      new_succ_flow_post@143@11
      (+
        (+
          (+ res@113@11 succ__globalInflowPost@116@11)
          (ite
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            new_prev_flow_post@141@11
            0))
        (ite (= prev@69@11 curr__next_pre@73@11) new_curr_flow_post@142@11 0)))
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
  (=
    new_prev_flow_post@141@11
    (+
      (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
      (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0))))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(assert (and
  (and
    (=
      new_succ_flow_post@143@11
      (+
        (+
          (+ res@113@11 succ__globalInflowPost@116@11)
          (ite
            (= prev__next_pre@70@11 curr__next_pre@73@11)
            new_prev_flow_post@141@11
            0))
        (ite (= prev@69@11 curr__next_pre@73@11) new_curr_flow_post@142@11 0)))
    (= new_curr_flow_post@142@11 (+ res@109@11 curr__globalInflowPost@112@11)))
  (=
    new_prev_flow_post@141@11
    (+
      (+ (+ res@105@11 prev__globalInflowPost@108@11) new_curr_flow_post@142@11)
      (ite (= res@94@11 prev@69@11) new_succ_flow_post@143@11 0)))))
(pop) ; 12
(push) ; 12
; [else-branch: 143 | !(new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11)]
(assert (not
  (and
    (and
      (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
      (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
    (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))))
(pop) ; 12
; [eval] !(new_prev_flow_post == new_prev_flow_post2 && (new_curr_flow_post == new_curr_flow_post2 && new_succ_flow_post == new_succ_flow_post2))
; [eval] new_prev_flow_post == new_prev_flow_post2 && (new_curr_flow_post == new_curr_flow_post2 && new_succ_flow_post == new_succ_flow_post2)
; [eval] new_prev_flow_post == new_prev_flow_post2
(push) ; 12
; [then-branch: 160 | new_prev_flow_post@141@11 == new_prev_flow_post2@148@11 | live]
; [else-branch: 160 | new_prev_flow_post@141@11 != new_prev_flow_post2@148@11 | live]
(push) ; 13
; [then-branch: 160 | new_prev_flow_post@141@11 == new_prev_flow_post2@148@11]
(assert (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))
; [eval] new_curr_flow_post == new_curr_flow_post2
(push) ; 14
; [then-branch: 161 | new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 | live]
; [else-branch: 161 | new_curr_flow_post@142@11 != new_curr_flow_post2@149@11 | live]
(push) ; 15
; [then-branch: 161 | new_curr_flow_post@142@11 == new_curr_flow_post2@149@11]
(assert (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
; [eval] new_succ_flow_post == new_succ_flow_post2
(pop) ; 15
(push) ; 15
; [else-branch: 161 | new_curr_flow_post@142@11 != new_curr_flow_post2@149@11]
(assert (not (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
; Joined path conditions
(assert (or
  (not (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11)))
(pop) ; 13
(push) ; 13
; [else-branch: 160 | new_prev_flow_post@141@11 != new_prev_flow_post2@148@11]
(assert (not (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(push) ; 12
(set-option :timeout 10)
(assert (not (and
  (and
    (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
    (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 12
(set-option :timeout 10)
(assert (not (not
  (and
    (and
      (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
      (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
    (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [then-branch: 162 | !(new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11) | live]
; [else-branch: 162 | new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11 | live]
(set-option :timeout 0)
(push) ; 12
; [then-branch: 162 | !(new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11)]
(assert (not
  (and
    (and
      (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
      (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
    (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11))))
; [exec]
; new_prev_flow_post := new_prev_flow_post2
; [exec]
; new_curr_flow_post := new_curr_flow_post2
; [exec]
; new_succ_flow_post := new_succ_flow_post2
; [exec]
; inhale prev__flow_post >= new_prev_flow_post
(declare-const $t@151@11 $Snap)
(assert (= $t@151@11 $Snap.unit))
; [eval] prev__flow_post >= new_prev_flow_post
(assert (>= res@103@11 new_prev_flow_post2@148@11))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr__flow_post >= new_curr_flow_post
(declare-const $t@152@11 $Snap)
(assert (= $t@152@11 $Snap.unit))
; [eval] curr__flow_post >= new_curr_flow_post
(assert (>= res@102@11 new_curr_flow_post2@149@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale succ__flow_post >= new_succ_flow_post
(declare-const $t@153@11 $Snap)
(assert (= $t@153@11 $Snap.unit))
; [eval] succ__flow_post >= new_succ_flow_post
(assert (>= res@101@11 new_succ_flow_post2@150@11))
; State saturation: after inhale
(check-sat)
; unknown
; Loop head block: Re-establish invariant
; [eval] fixpoint2 ==> new_prev_flow_post == prev__externalInflow + prev__globalInflowPost + (prev__next_post == prev ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == prev ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == prev ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && (new_curr_flow_post == curr__externalInflow + curr__globalInflowPost + (prev__next_post == curr ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == curr ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == curr ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0) && new_succ_flow_post == succ__externalInflow + succ__globalInflowPost + (prev__next_post == succ ? (new_prev_flow_post >= 3 ? 3 : new_prev_flow_post) : 0) + (curr__next_post == succ ? (new_curr_flow_post >= 3 ? 3 : new_curr_flow_post) : 0) + (succ__next_post == succ ? (new_succ_flow_post >= 3 ? 3 : new_succ_flow_post) : 0))
(set-option :timeout 0)
(push) ; 13
; [then-branch: 163 | fixpoint2@140@11 | dead]
; [else-branch: 163 | !(fixpoint2@140@11) | live]
(push) ; 14
; [else-branch: 163 | !(fixpoint2@140@11)]
(pop) ; 14
(pop) ; 13
; Joined path conditions
(pop) ; 12
(push) ; 12
; [else-branch: 162 | new_succ_flow_post@143@11 == new_succ_flow_post2@150@11 && new_curr_flow_post@142@11 == new_curr_flow_post2@149@11 && new_prev_flow_post@141@11 == new_prev_flow_post2@148@11]
(assert (and
  (and
    (= new_succ_flow_post@143@11 new_succ_flow_post2@150@11)
    (= new_curr_flow_post@142@11 new_curr_flow_post2@149@11))
  (= new_prev_flow_post@141@11 new_prev_flow_post2@148@11)))
(pop) ; 12
(pop) ; 11
(push) ; 11
; [else-branch: 127 | fixpoint2@140@11]
(assert fixpoint2@140@11)
(pop) ; 11
; [eval] !!fixpoint2
; [eval] !fixpoint2
(push) ; 11
(set-option :timeout 10)
(assert (not (not fixpoint2@140@11)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(set-option :timeout 10)
(assert (not fixpoint2@140@11))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [then-branch: 164 | fixpoint2@140@11 | live]
; [else-branch: 164 | !(fixpoint2@140@11) | live]
(set-option :timeout 0)
(push) ; 11
; [then-branch: 164 | fixpoint2@140@11]
(assert fixpoint2@140@11)
; [exec]
; inhale prev__flow_post == new_prev_flow_post
(declare-const $t@154@11 $Snap)
(assert (= $t@154@11 $Snap.unit))
; [eval] prev__flow_post == new_prev_flow_post
(assert (= res@103@11 new_prev_flow_post@141@11))
; State saturation: after inhale
(set-option :timeout 20)
(check-sat)
; unknown
; [exec]
; inhale curr__flow_post == new_curr_flow_post
(declare-const $t@155@11 $Snap)
(assert (= $t@155@11 $Snap.unit))
; [eval] curr__flow_post == new_curr_flow_post
(assert (= res@102@11 new_curr_flow_post@142@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale succ__flow_post == new_succ_flow_post
(declare-const $t@156@11 $Snap)
(assert (= $t@156@11 $Snap.unit))
; [eval] succ__flow_post == new_succ_flow_post
(assert (= res@101@11 new_succ_flow_post@143@11))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale node != prev
(declare-const $t@157@11 $Snap)
(assert (= $t@157@11 $Snap.unit))
; [eval] node != prev
(assert (not (= node@93@11 prev@69@11)))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale node != curr
(declare-const $t@158@11 $Snap)
(assert (= $t@158@11 $Snap.unit))
; [eval] node != curr
(assert (not (= node@93@11 curr@72@11)))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale node != succ
(declare-const $t@159@11 $Snap)
(assert (= $t@159@11 $Snap.unit))
; [eval] node != succ
(assert (not (= node@93@11 curr__next_pre@73@11)))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; inhale node > -1
(declare-const $t@160@11 $Snap)
(assert (= $t@160@11 $Snap.unit))
; [eval] node > -1
; [eval] -1
(assert (> node@93@11 (- 0 1)))
; State saturation: after inhale
(check-sat)
; unknown
; [exec]
; assert (node == prev__next_pre ?
;     (prev__flow_pre >= 3 ? 3 : prev__flow_pre) :
;     0) +
;   (node == curr__next_pre ? (curr__flow_pre >= 3 ? 3 : curr__flow_pre) : 0) +
;   (node == succ__next_pre ? (succ__flow_pre >= 3 ? 3 : succ__flow_pre) : 0) ==
;   (node == prev__next_post ?
;     (prev__flow_post >= 3 ? 3 : prev__flow_post) :
;     0) +
;   (node == curr__next_post ?
;     (curr__flow_post >= 3 ? 3 : curr__flow_post) :
;     0) +
;   (node == succ__next_post ?
;     (succ__flow_post >= 3 ? 3 : succ__flow_post) :
;     0)
; [eval] (node == prev__next_pre ? (prev__flow_pre >= 3 ? 3 : prev__flow_pre) : 0) + (node == curr__next_pre ? (curr__flow_pre >= 3 ? 3 : curr__flow_pre) : 0) + (node == succ__next_pre ? (succ__flow_pre >= 3 ? 3 : succ__flow_pre) : 0) == (node == prev__next_post ? (prev__flow_post >= 3 ? 3 : prev__flow_post) : 0) + (node == curr__next_post ? (curr__flow_post >= 3 ? 3 : curr__flow_post) : 0) + (node == succ__next_post ? (succ__flow_post >= 3 ? 3 : succ__flow_post) : 0)
; [eval] (node == prev__next_pre ? (prev__flow_pre >= 3 ? 3 : prev__flow_pre) : 0) + (node == curr__next_pre ? (curr__flow_pre >= 3 ? 3 : curr__flow_pre) : 0) + (node == succ__next_pre ? (succ__flow_pre >= 3 ? 3 : succ__flow_pre) : 0)
; [eval] (node == prev__next_pre ? (prev__flow_pre >= 3 ? 3 : prev__flow_pre) : 0) + (node == curr__next_pre ? (curr__flow_pre >= 3 ? 3 : curr__flow_pre) : 0)
; [eval] (node == prev__next_pre ? (prev__flow_pre >= 3 ? 3 : prev__flow_pre) : 0)
; [eval] node == prev__next_pre
(set-option :timeout 0)
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= node@93@11 prev__next_pre@70@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= node@93@11 prev__next_pre@70@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 165 | node@93@11 == prev__next_pre@70@11 | live]
; [else-branch: 165 | node@93@11 != prev__next_pre@70@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 165 | node@93@11 == prev__next_pre@70@11]
(assert (= node@93@11 prev__next_pre@70@11))
; [eval] (prev__flow_pre >= 3 ? 3 : prev__flow_pre)
; [eval] prev__flow_pre >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= prev__flow_pre@71@11 3))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 166 | prev__flow_pre@71@11 >= 3 | dead]
; [else-branch: 166 | !(prev__flow_pre@71@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 166 | !(prev__flow_pre@71@11 >= 3)]
(assert (not (>= prev__flow_pre@71@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (>= prev__flow_pre@71@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 165 | node@93@11 != prev__next_pre@70@11]
(assert (not (= node@93@11 prev__next_pre@70@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= node@93@11 prev__next_pre@70@11)
  (and (= node@93@11 prev__next_pre@70@11) (not (>= prev__flow_pre@71@11 3)))))
; Joined path conditions
(assert (or
  (not (= node@93@11 prev__next_pre@70@11))
  (= node@93@11 prev__next_pre@70@11)))
; [eval] (node == curr__next_pre ? (curr__flow_pre >= 3 ? 3 : curr__flow_pre) : 0)
; [eval] node == curr__next_pre
(push) ; 12
; [then-branch: 167 | node@93@11 == curr__next_pre@73@11 | dead]
; [else-branch: 167 | node@93@11 != curr__next_pre@73@11 | live]
(push) ; 13
; [else-branch: 167 | node@93@11 != curr__next_pre@73@11]
(pop) ; 13
(pop) ; 12
; Joined path conditions
; [eval] (node == succ__next_pre ? (succ__flow_pre >= 3 ? 3 : succ__flow_pre) : 0)
; [eval] node == succ__next_pre
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= node@93@11 res@94@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= node@93@11 res@94@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 168 | node@93@11 == res@94@11 | live]
; [else-branch: 168 | node@93@11 != res@94@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 168 | node@93@11 == res@94@11]
(assert (= node@93@11 res@94@11))
; [eval] (succ__flow_pre >= 3 ? 3 : succ__flow_pre)
; [eval] succ__flow_pre >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= res@95@11 3))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 169 | res@95@11 >= 3 | dead]
; [else-branch: 169 | !(res@95@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 169 | !(res@95@11 >= 3)]
(assert (not (>= res@95@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (>= res@95@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 168 | node@93@11 != res@94@11]
(assert (not (= node@93@11 res@94@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= node@93@11 res@94@11)
  (and (= node@93@11 res@94@11) (not (>= res@95@11 3)))))
; Joined path conditions
(assert (or (not (= node@93@11 res@94@11)) (= node@93@11 res@94@11)))
; [eval] (node == prev__next_post ? (prev__flow_post >= 3 ? 3 : prev__flow_post) : 0) + (node == curr__next_post ? (curr__flow_post >= 3 ? 3 : curr__flow_post) : 0) + (node == succ__next_post ? (succ__flow_post >= 3 ? 3 : succ__flow_post) : 0)
; [eval] (node == prev__next_post ? (prev__flow_post >= 3 ? 3 : prev__flow_post) : 0) + (node == curr__next_post ? (curr__flow_post >= 3 ? 3 : curr__flow_post) : 0)
; [eval] (node == prev__next_post ? (prev__flow_post >= 3 ? 3 : prev__flow_post) : 0)
; [eval] node == prev__next_post
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= node@93@11 prev__next_pre@70@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= node@93@11 prev__next_pre@70@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 170 | node@93@11 == prev__next_pre@70@11 | live]
; [else-branch: 170 | node@93@11 != prev__next_pre@70@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 170 | node@93@11 == prev__next_pre@70@11]
(assert (= node@93@11 prev__next_pre@70@11))
; [eval] (prev__flow_post >= 3 ? 3 : prev__flow_post)
; [eval] prev__flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= res@103@11 3))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 171 | res@103@11 >= 3 | dead]
; [else-branch: 171 | !(res@103@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 171 | !(res@103@11 >= 3)]
(assert (not (>= res@103@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (>= res@103@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 170 | node@93@11 != prev__next_pre@70@11]
(assert (not (= node@93@11 prev__next_pre@70@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= node@93@11 prev__next_pre@70@11)
  (and (= node@93@11 prev__next_pre@70@11) (not (>= res@103@11 3)))))
; Joined path conditions
; [eval] (node == curr__next_post ? (curr__flow_post >= 3 ? 3 : curr__flow_post) : 0)
; [eval] node == curr__next_post
(push) ; 12
; [then-branch: 172 | node@93@11 == prev@69@11 | dead]
; [else-branch: 172 | node@93@11 != prev@69@11 | live]
(push) ; 13
; [else-branch: 172 | node@93@11 != prev@69@11]
(pop) ; 13
(pop) ; 12
; Joined path conditions
; [eval] (node == succ__next_post ? (succ__flow_post >= 3 ? 3 : succ__flow_post) : 0)
; [eval] node == succ__next_post
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= node@93@11 res@94@11))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= node@93@11 res@94@11)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 173 | node@93@11 == res@94@11 | live]
; [else-branch: 173 | node@93@11 != res@94@11 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 173 | node@93@11 == res@94@11]
(assert (= node@93@11 res@94@11))
; [eval] (succ__flow_post >= 3 ? 3 : succ__flow_post)
; [eval] succ__flow_post >= 3
(push) ; 14
(push) ; 15
(set-option :timeout 10)
(assert (not (not (>= res@101@11 3))))
(check-sat)
; unsat
(pop) ; 15
; 0.00s
; (get-info :all-statistics)
; [then-branch: 174 | res@101@11 >= 3 | dead]
; [else-branch: 174 | !(res@101@11 >= 3) | live]
(set-option :timeout 0)
(push) ; 15
; [else-branch: 174 | !(res@101@11 >= 3)]
(assert (not (>= res@101@11 3)))
(pop) ; 15
(pop) ; 14
; Joined path conditions
(assert (not (>= res@101@11 3)))
(pop) ; 13
(push) ; 13
; [else-branch: 173 | node@93@11 != res@94@11]
(assert (not (= node@93@11 res@94@11)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
(assert (=>
  (= node@93@11 res@94@11)
  (and (= node@93@11 res@94@11) (not (>= res@101@11 3)))))
; Joined path conditions
(push) ; 12
(assert (not (=
  (+
    (ite (= node@93@11 prev__next_pre@70@11) prev__flow_pre@71@11 0)
    (ite (= node@93@11 res@94@11) res@95@11 0))
  (+
    (ite (= node@93@11 prev__next_pre@70@11) res@103@11 0)
    (ite (= node@93@11 res@94@11) res@101@11 0)))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (=
  (+
    (ite (= node@93@11 prev__next_pre@70@11) prev__flow_pre@71@11 0)
    (ite (= node@93@11 res@94@11) res@95@11 0))
  (+
    (ite (= node@93@11 prev__next_pre@70@11) res@103@11 0)
    (ite (= node@93@11 res@94@11) res@101@11 0))))
; [exec]
; assert curr >= -1 &&
;   (curr__flow_post == (curr != -1 ? 1 : 2) &&
;   ((curr == -1 ==> curr__next_post < -1) && true))
; [eval] curr >= -1
; [eval] -1
; [eval] curr__flow_post == (curr != -1 ? 1 : 2)
; [eval] (curr != -1 ? 1 : 2)
; [eval] curr != -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 175 | curr@72@11 != -1 | live]
; [else-branch: 175 | curr@72@11 == -1 | dead]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 175 | curr@72@11 != -1]
(pop) ; 13
(pop) ; 12
; Joined path conditions
(push) ; 12
(assert (not (= res@102@11 1)))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (= res@102@11 1))
; [eval] curr == -1 ==> curr__next_post < -1
; [eval] curr == -1
; [eval] -1
(push) ; 12
; [then-branch: 176 | curr@72@11 == -1 | dead]
; [else-branch: 176 | curr@72@11 != -1 | live]
(push) ; 13
; [else-branch: 176 | curr@72@11 != -1]
(pop) ; 13
(pop) ; 12
; Joined path conditions
; [exec]
; assert prev >= -1 &&
;   (prev__flow_post == (prev != -1 ? 1 : 2) &&
;   ((prev == -1 ==> prev__next_post < -1) && true))
; [eval] prev >= -1
; [eval] -1
; [eval] prev__flow_post == (prev != -1 ? 1 : 2)
; [eval] (prev != -1 ? 1 : 2)
; [eval] prev != -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (= prev@69@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev@69@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 177 | prev@69@11 != -1 | live]
; [else-branch: 177 | prev@69@11 == -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 177 | prev@69@11 != -1]
(assert (not (= prev@69@11 (- 0 1))))
(pop) ; 13
(push) ; 13
; [else-branch: 177 | prev@69@11 == -1]
(assert (= prev@69@11 (- 0 1)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(push) ; 12
(assert (not (= res@103@11 (ite (not (= prev@69@11 (- 0 1))) 1 2))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (= res@103@11 (ite (not (= prev@69@11 (- 0 1))) 1 2)))
; [eval] prev == -1 ==> prev__next_post < -1
; [eval] prev == -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= prev@69@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= prev@69@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 178 | prev@69@11 == -1 | live]
; [else-branch: 178 | prev@69@11 != -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 178 | prev@69@11 == -1]
(assert (= prev@69@11 (- 0 1)))
; [eval] prev__next_post < -1
; [eval] -1
(pop) ; 13
(push) ; 13
; [else-branch: 178 | prev@69@11 != -1]
(assert (not (= prev@69@11 (- 0 1))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [exec]
; assert succ >= -1 &&
;   (succ__flow_post == (succ != -1 ? 1 : 2) &&
;   ((succ == -1 ==> succ__next_post < -1) && true))
; [eval] succ >= -1
; [eval] -1
; [eval] succ__flow_post == (succ != -1 ? 1 : 2)
; [eval] (succ != -1 ? 1 : 2)
; [eval] succ != -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 179 | curr__next_pre@73@11 != -1 | live]
; [else-branch: 179 | curr__next_pre@73@11 == -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 179 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 13
(push) ; 13
; [else-branch: 179 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
(push) ; 12
(assert (not (= res@101@11 (ite (not (= curr__next_pre@73@11 (- 0 1))) 1 2))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (= res@101@11 (ite (not (= curr__next_pre@73@11 (- 0 1))) 1 2)))
; [eval] succ == -1 ==> succ__next_post < -1
; [eval] succ == -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 180 | curr__next_pre@73@11 == -1 | live]
; [else-branch: 180 | curr__next_pre@73@11 != -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 180 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
; [eval] succ__next_post < -1
; [eval] -1
(pop) ; 13
(push) ; 13
; [else-branch: 180 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [exec]
; prev := curr
; [exec]
; prev__next_pre := curr__next_post
; [exec]
; prev__flow_pre := curr__flow_post
; [exec]
; curr := succ
; [exec]
; curr__next_pre := succ__next_post
; [exec]
; curr__flow_pre := succ__flow_post
; Loop head block: Re-establish invariant
; [eval] curr >= -1
; [eval] -1
; [eval] curr__flow_pre == (curr != -1 ? 1 : 2)
; [eval] (curr != -1 ? 1 : 2)
; [eval] curr != -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 181 | curr__next_pre@73@11 != -1 | live]
; [else-branch: 181 | curr__next_pre@73@11 == -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 181 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 13
(push) ; 13
; [else-branch: 181 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [eval] curr == -1 ==> curr__next_pre < -1
; [eval] curr == -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (not (= curr__next_pre@73@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 182 | curr__next_pre@73@11 == -1 | live]
; [else-branch: 182 | curr__next_pre@73@11 != -1 | live]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 182 | curr__next_pre@73@11 == -1]
(assert (= curr__next_pre@73@11 (- 0 1)))
; [eval] curr__next_pre < -1
; [eval] -1
(pop) ; 13
(push) ; 13
; [else-branch: 182 | curr__next_pre@73@11 != -1]
(assert (not (= curr__next_pre@73@11 (- 0 1))))
(pop) ; 13
(pop) ; 12
; Joined path conditions
; Joined path conditions
; [eval] prev >= -1
; [eval] -1
; [eval] prev__flow_pre == (prev != -1 ? 1 : 2)
; [eval] (prev != -1 ? 1 : 2)
; [eval] prev != -1
; [eval] -1
(push) ; 12
(push) ; 13
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [then-branch: 183 | curr@72@11 != -1 | live]
; [else-branch: 183 | curr@72@11 == -1 | dead]
(set-option :timeout 0)
(push) ; 13
; [then-branch: 183 | curr@72@11 != -1]
(pop) ; 13
(pop) ; 12
; Joined path conditions
; [eval] prev == -1 ==> prev__next_pre < -1
; [eval] prev == -1
; [eval] -1
(push) ; 12
; [then-branch: 184 | curr@72@11 == -1 | dead]
; [else-branch: 184 | curr@72@11 != -1 | live]
(push) ; 13
; [else-branch: 184 | curr@72@11 != -1]
(pop) ; 13
(pop) ; 12
; Joined path conditions
; [eval] HeadLeftPost == curr
; [eval] HeadRightPost == prev
(pop) ; 11
(push) ; 11
; [else-branch: 164 | !(fixpoint2@140@11)]
(assert (not fixpoint2@140@11))
(pop) ; 11
(pop) ; 10
(pop) ; 9
(pop) ; 8
(push) ; 8
; [else-branch: 109 | !(fixpoint1@120@11)]
(assert (not fixpoint1@120@11))
(pop) ; 8
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch: 12 | curr@72@11 == -1]
(assert (= curr@72@11 (- 0 1)))
(pop) ; 5
; [eval] !(curr != -1)
; [eval] curr != -1
; [eval] -1
(push) ; 5
(set-option :timeout 10)
(assert (not (not (= curr@72@11 (- 0 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(set-option :timeout 10)
(assert (not (= curr@72@11 (- 0 1))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [then-branch: 185 | curr@72@11 == -1 | live]
; [else-branch: 185 | curr@72@11 != -1 | live]
(set-option :timeout 0)
(push) ; 5
; [then-branch: 185 | curr@72@11 == -1]
(assert (= curr@72@11 (- 0 1)))
(pop) ; 5
(push) ; 5
; [else-branch: 185 | curr@72@11 != -1]
(assert (not (= curr@72@11 (- 0 1))))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
(pop) ; 1

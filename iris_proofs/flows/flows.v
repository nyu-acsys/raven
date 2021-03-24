(** Theory of Flow Interface *)

(* This formalization builds on the paper:
   
   Local Reasoning for Global Graph Properties: Siddharth Krishna and Alexander J. Summers and Thomas Wies, ESOP'20.
*)

From iris.algebra Require Export auth updates local_updates.
From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
Require Export ccm gmap_more.
Require Import Coq.Setoids.Setoid.

(* The set of nodes over which graphs are built. *)
Definition Node := nat.

Section flowint.

(* The underlying flow domain. *)
Context `{CCM flowdom}.

Open Scope ccm_scope.

(* Representation of flow interfaces: 
   - The domain of the interface is the domain of its inflow infR. 
   - The outflow function is defined using nzmap so that interface composition is cancelable. 
*)
Record flowintR :=
  {
    infR : gmap Node flowdom;
    outR : nzmap Node flowdom;
  }.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT. (* used when interface composition is undefined *)

(* The empty interface *)
Definition I_emptyR := {| infR := ∅; outR := ∅ |}.
Definition I_empty := int I_emptyR.
Global Instance flowint_empty : Empty flowintT := I_empty.

(* Some auxiliary function for accessing the components of an interface *)
Definition out_map (I: flowintT) :=
  match I with
    | int Ir => outR Ir
    | intUndef => ∅
  end.

Definition inf_map (I: flowintT) :=
  match I with
    | int Ir => infR Ir
    | intUndef => ∅
  end.

Definition inf (I: flowintT) (n: Node) := default 0 (inf_map I !! n).
Definition out (I: flowintT) (n: Node) := out_map I ! n.

Global Instance flowint_dom : Dom flowintT (gset Node) :=
  λ I, dom (gset Node) (inf_map I).
Definition domm (I : flowintT) := dom (gset Node) I.

Global Instance flowint_elem_of : ElemOf Node flowintT :=
  λ n I, n ∈ domm I.

(* Some useful implicit type classes *)

Canonical Structure flowintRAC := leibnizO flowintT.

Global Instance int_eq_dec: EqDecision flowintT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  - apply nzmap_eq_eq.
  - apply gmap_eq_eq.
Qed.

(** Interface validity *)

Global Instance flowint_valid : Valid flowintT :=
  λ I, match I with
       | int Ir =>
         infR Ir ##ₘ nzmap_car (outR Ir)
         ∧ (infR Ir = ∅ → outR Ir = ∅)
       | intUndef => False
       end.

Global Instance flowint_valid_dec : ∀ I: flowintT, Decision (✓ I).
Proof.
  intros.
  unfold valid; unfold flowint_valid.
  destruct I.
  all: solve_decision.
Qed.

(** Predicate that holds true iff two interfaces are composable *)
                                                                  
Definition intComposable (I1: flowintT) (I2: flowintT) :=
  ✓ I1 ∧ ✓ I2 ∧
  domm I1 ## domm I2 ∧
  map_Forall (λ (n: Node) (m: flowdom), m = out I2 n + (inf I1 n - out I2 n)) (inf_map I1) ∧
  map_Forall (λ (n: Node) (m: flowdom), m = out I1 n + (inf I2 n - out I1 n)) (inf_map I2).

Global Instance intComposable_dec (I1 I2: flowintT) : Decision (intComposable I1 I2).
Proof.
  solve_decision.
Qed.

(** Interface composition *)

(* Function to compute outflow of composite interface *)
Definition outComp_op I1 I2 n (m1 m2 : flowdom) :=
  if decide (n ∈ domm I1 ∪ domm I2) then 0 else m1 + m2.

Global Instance outComp_unit_id : ∀ n I1 I2, UnitId _ _ (outComp_op I1 I2 n).
Proof.
  intros.
  unfold UnitId, outComp_op.
  destruct (decide _).
  all: auto using ccm_right_id.
Qed.

Definition outComp I1 I2 :=
  nzmap_imerge (outComp_op I1 I2) (out_map I1) (out_map I2).

Lemma outComp_inv I1 I2 :
  ∀ n, n ∉ domm I1 ∪ domm I2 → outComp I1 I2 ! n = out I1 n + out I2 n.
Proof.
  intros n D.
  unfold outComp.
  rewrite nzmap_lookup_imerge.
  unfold outComp_op.
  destruct (decide _).
  - contradiction.
  - unfold out.
    reflexivity.
Qed.

(* Function to compute inflow of composite interface *)
Definition infComp_op I1 I2 n (o1 o2 : option flowdom) :=
  match o1, o2 with
  | Some m1, _ => Some (m1 - out I2 n)
  | _, Some m2 => Some (m2 - out I1 n)
  | _, _ => None
  end.

Global Instance infComp_diag_none : ∀ I1 I2 n, DiagNone (infComp_op I1 I2 n).
Proof.
  intros.
  unfold DiagNone, infComp_op.
  auto.
Defined.

Definition infComp I1 I2 := gmap_imerge (infComp_op I1 I2) (inf_map I1) (inf_map I2).

(* The actual interface composition *)
Global Instance intComp : Op flowintT :=
  λ I1 I2, if decide (intComposable I1 I2) then
             int {| infR := infComp I1 I2 ; outR := outComp I1 I2 |}
           else if decide (I1 = ∅) then I2
           else if decide (I2 = ∅) then I1
           else intUndef.

(** Assorted auxiliary lemmas. These are used, in particular, to prove that flow interfaces form a camera. *)

(* The empty interface has no outflow. *)
Lemma intEmp_out : ∀ n, out I_empty n = 0.
Proof.
  intros.
  unfold out, I_empty, out_map, I_emptyR.
  simpl.
  apply nzmap_lookup_empty.
Qed.

(* Expansion of interface validity *)
Lemma intValid_unfold : ∀ I, ✓ I ↔
                             I ≠ intUndef
                             ∧ inf_map I ##ₘ nzmap_car (out_map I)
                             ∧ (inf_map I = ∅ → out_map I = ∅).
Proof.
  intros I.
  split.
  - intros HIv.
    unfold valid, flowint_valid in HIv.
    destruct I as [Ir |].
    + split.
      * discriminate.
      * unfold inf_map, out_map. trivial.
    + contradiction.
        
  - intros HIv.
    destruct HIv as [HIv0 HIv1].
    destruct I as [Ir |].
    + unfold valid, flowint_valid.
      unfold inf_map, out_map in HIv1. trivial.
    + contradiction.
Qed.
 

(* Valid interfaces don't give outflow to nodes in their domain. *)
Lemma intValid_in_dom_not_out : ∀ I n, ✓ I → n ∈ domm I → out I n = 0.
Proof.
  intros ? ? V D.
  unfold valid, flowint_valid in V.
  destruct I as [Ir |].
  - destruct V as (Disj & _).
    assert (dom (gset Node) (infR Ir) ## dom (gset Node) (nzmap_car (outR Ir))).
    apply map_disjoint_dom. trivial.
    unfold domm, dom, flowint_dom, inf_map in D.
    assert (n ∉ dom (gset Node) (outR Ir)).
    { unfold dom, nzmap_dom.
      set_solver.
    }
    rewrite nzmap_elem_of_dom_total in H1 *.
    intros.
    apply dec_stable in H1.
    trivial.
  - contradiction.
Qed.

(* The empty interface is valid. *)
Lemma intEmp_valid : ✓ I_empty.
Proof.
  unfold valid.
  unfold flowint_valid.
  unfold I_empty.
  simpl.
  split.
  refine (map_disjoint_empty_l _).
  trivial.
Qed.

(* The empty interface is the unique valid interface whose domain is empty. *)
Lemma intEmp_unique I : ✓ I → domm I ≡ ∅ → I = ∅.
Proof.
  intros V D.
  unfold valid, flowint_valid in V.
  destruct I as [Ir |].
  destruct V as (? & V).
  unfold domm, dom, flowint_dom, inf_map in D.
  unfold empty, flowint_empty, I_empty.
  apply f_equal.
  unfold I_emptyR.
  destruct Ir as [Iinf Iout].
  simpl in V.
  simpl in D.
  apply (dom_empty_inv Iinf) in D.
  pose proof (V D) as O.
  rewrite D.
  rewrite O.
  reflexivity.
  contradiction.
Qed.


(* The undefined interface is not valid. *)
Lemma intUndef_not_valid : ¬ ✓ intUndef.
Proof. unfold valid, flowint_valid; auto. Qed.

(* Invalid interfaces are not composable. *)
Lemma intComposable_invalid : ∀ I1 I2, ¬ ✓ I1 → ¬ (intComposable I1 I2).
Proof.
  intros.
  unfold intComposable.
  unfold not.
  intros H_false.
  destruct H_false as [H_false _].
  now contradict H_false.
Qed.

(* Composing with an invalid interface yields an invalid interface. *)
Lemma intComp_invalid : ∀ I1 I2: flowintT, ¬ ✓ I1 → ¬ ✓ (I1 ⋅ I2).
Proof.
  intros.
  unfold op, intComp.
  rewrite decide_False; last by apply intComposable_invalid.
  rewrite decide_False; last first.
  unfold not. intros H_false.
  contradict H0.
  rewrite H_false.
  apply intEmp_valid.
  destruct (decide (I2 = ∅)).
  auto.
  apply intUndef_not_valid.
Qed.

(* Composing with the undefined interface is undefined. *)
Lemma intComp_undef_op : ∀ I, intUndef ⋅ I ≡ intUndef.
Proof.
 intros.
  unfold op; unfold intComp.
  rewrite decide_False.
  unfold empty.
  unfold flowint_empty.
  rewrite decide_False.
  destruct (decide (I = I_empty)).
  1, 2: trivial.
  discriminate.
  unfold intComposable.
  cut (¬ (✓ intUndef)); intros.
  rewrite stdpp.base.left_absorb.
  trivial.
  unfold valid; unfold flowint_valid.
  auto.
Qed.

(* The empty interface is the right identity of interface composition. *)
Lemma intComp_unit : ∀ (I: flowintT), I ⋅ I_empty ≡ I.
Proof.
  intros.
  unfold op, intComp, outComp.
  simpl.
  destruct I as [Ir|].
  destruct (decide (intComposable (int Ir) I_empty)).
  - (* True *)
    unfold infComp.
    rewrite gmap_imerge_empty.
    f_equal.
    * destruct Ir.
      f_equal.
      apply nzmap_eq.
      intros.
      rewrite nzmap_lookup_imerge.
      unfold outComp_op.
      destruct (decide _).
      unfold domm in e.
      rewrite elem_of_union in e *.
      intros.
      destruct H0.
      unfold intComposable in i.
      destruct i as (V & _).
      unfold valid, flowint_valid in V.
      destruct V as (V & _).
      simpl in V.
      assert (dom (gset Node) infR0 ## dom (gset Node) (nzmap_car outR0)).
      rewrite <- map_disjoint_dom.
      trivial.
      unfold flowint_dom, inf_map in H0.
      simpl in H0.
      unfold nzmap_total_lookup.
      destruct (outR0 !! k) eqn:?.
      assert (k ∈ dom (gset Node) outR0).
      unfold dom, nzmap_dom.
      rewrite elem_of_dom.
      unfold is_Some.
      exists f.
      unfold lookup, nzmap_lookup in Heqo.
      destruct outR0.
      simpl.
      trivial.
      assert (k ∉ dom (gset Node) outR0).
      set_solver.
      contradiction.
      trivial.
      unfold dom, flowint_dom, I_empty, I_emptyR in H0. simpl in H0.
      rewrite dom_empty in H0 *.
      intros.
      rewrite elem_of_empty in H0 *.
      naive_solver.
      rewrite nzmap_lookup_empty.
      unfold out_map.
      rewrite ccm_right_id.
      auto.
    * intros.
      case y.
      intros.
      unfold infComp_op.
      rewrite intEmp_out.
      by rewrite ccm_pinv_unit.
      auto.
  - (* False *)
    destruct (decide _).
    unfold empty, flowint_empty in e.
    rewrite e.
    reflexivity.
    destruct (decide _).
    reflexivity.
    unfold empty, flowint_empty in n1.
    contradiction.
  - unfold intComposable.
    rewrite decide_False.
    rewrite decide_False.
    rewrite decide_True.
    all: auto.
    unfold not; intros (H_false & _).
    contradict H_false.
Qed.

(* The intComposable predicate is commutative. *)
Lemma intComposable_comm_1 : ∀ (I1 I2 : flowintT), intComposable I1 I2 → intComposable I2 I1.
Proof.
  intros.
  unfold intComposable.
  repeat split.
  3: apply disjoint_intersection; rewrite intersection_comm_L; apply disjoint_intersection.
  unfold intComposable in H0.
  all: try apply H0.
Qed.

Lemma intComposable_comm : ∀ (I1 I2 : flowintT), intComposable I1 I2 ↔ intComposable I2 I1.
Proof.
  intros. split.
  all: refine (intComposable_comm_1 _ _).
Qed.

(* The domain of a composite interface is the union of the domain of its component interfaces. *)
Lemma infComp_dom : ∀ I1 I2, dom (gset Node) (infComp I1 I2) = domm I1 ∪ domm I2.
Proof.
  intros.
  unfold domm.
  set_unfold.
  intros.
  rewrite ?elem_of_dom.
  unfold infComp.
  rewrite gmap_imerge_prf.
  unfold dom, flowint_dom.
  repeat rewrite elem_of_dom.
  unfold infComp_op.
  case_eq (inf_map I1 !! x).
    + intros ? H1.
      (*rewrite H1.*)
      rewrite ?is_Some_alt; simpl.
      naive_solver.
    + intros H1.
      (*rewrite H1.*)
      case_eq (inf_map I2 !! x).
      * intros ? H2.
        (*rewrite H2.*)
        rewrite ?is_Some_alt; simpl.
        naive_solver.
      * intros H2.
        (*rewrite H2.*)
        split.
        apply or_introl.
        intros.
        destruct H.
        all: clear - H0; firstorder.
Qed.

Lemma intComp_dom : ∀ I1 I2, ✓ (I1 ⋅ I2) → domm (I1 ⋅ I2) = domm I1 ∪ domm I2.
Proof.
  intros I1 I2 H_valid.
  unfold op, intComp.
  case_eq (decide (intComposable I1 I2)).
  - intros.
    unfold domm at 1, dom, flowint_dom. simpl.
    by rewrite infComp_dom.
  - unfold domm.
    set_unfold.
    intros.
    unfold dom.
    rewrite ?elem_of_dom.
    case_eq (decide (I1 = ∅)).
    + intros H1 H1_dec.
      rewrite H1.
      simpl.
      rewrite lookup_empty.
      split.
      apply or_intror.
      intros H_or; destruct H_or as [H_false | H2].
      contradict H_false.
      exact is_Some_None.
      exact H2.
    + intros H1 H1_dec.
      case_eq (decide (I2 = ∅)).
      * intros H2 H2_dec.
        rewrite H2; simpl.
        rewrite lookup_empty.
        split.
        apply or_introl.
        intros H_or; destruct H_or.
        assumption.
        contradict H3.
        exact is_Some_None.
      * intros H2 H2_dec.
        contradict H_valid.
        unfold op, intComp.
        rewrite H0. rewrite H1_dec. rewrite H2_dec.
        exact intUndef_not_valid.
Qed.

(* Interface composition is commutative. *)
Lemma intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.
Proof.
  intros.
  cut (∀ I, intUndef ⋅ I ≡ I ⋅ intUndef).
  intros H_undef_comm.
  destruct I1 as [ir1|] eqn:H_eq1, I2 as [ir2|] eqn:H_eq2; revgoals.
  all: try rewrite H_undef_comm; auto.
  unfold op, intComp, infComp, outComp; simpl.
  case_eq (decide (intComposable (int ir1) (int ir2))).
  - (* if composable *)
    intros H_comp H_comp_dec.
    rewrite decide_True; last rewrite intComposable_comm; auto.
    f_equal.
    f_equal.
    + (* infR equality *)
      rewrite map_eq_iff.
      intros.
      repeat rewrite gmap_imerge_prf; auto.
      case_eq (infR ir1 !! i).
      all: case_eq (infR ir2 !! i).
      * (* i in both *)
        intros f1 H_lookup2 f2 H_lookup1.
        exfalso.
        generalize H_comp.
        unfold intComposable.
        intros (_ & _ & H_false & _).
        unfold domm, dom, flowint_dom in H_false.
        simpl in *.
        rewrite <- map_disjoint_dom in H_false.
        generalize H_false. clear H_false.
        rewrite map_disjoint_alt.
        intros H_false.
        assert (H_contra := H_false i).
        destruct H_contra.
        contradict H0.
        now rewrite H_lookup1.
        contradict H0.
        now rewrite H_lookup2.
      * (* in I1 but not in I2 *)
        intros H_lookup2 f1 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
      * (* in I2 but not in I1 *)
        intros f2 H_lookup2 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
      * (* in neither *)
        intros H_lookup2 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
    + (* outR equality *)
      apply nzmap_eq.
      intros.
      repeat rewrite nzmap_lookup_imerge.
      unfold outComp_op.
      pose proof (union_comm (domm (int ir1)) (domm (int ir2))).
      repeat destruct (decide (k ∈ _)); try auto;
      try (rewrite H0 in e *; naive_solver).
      try (rewrite H0 in n *; naive_solver).
      by rewrite ccm_comm.
  - (* if not composable *)
    intros H_not_comp H_not_comp_dec.
    symmetry.
    rewrite decide_False; last by rewrite intComposable_comm.
    case_eq (decide (int ir2 = ∅)).
    case_eq (decide (int ir1 = ∅)).
    all: auto.
    intros.
    now rewrite e e0.
  - (* proof of H_undef_comm *)
    intros.
    rewrite intComp_undef_op.
    unfold op, flowint_valid, intComp.
    rewrite decide_False.
    case (decide (I = ∅)).
    all: auto.
    intros _.
    rewrite decide_False.
    all: auto.
    unfold intComposable.
    rewrite ?not_and_l.
    right. left.
    exact intUndef_not_valid.
Qed.

(* The empty interface is also a left identity of interface composition. *)
Lemma intComp_left_unit : ∀ I : flowintT, I_empty ⋅ I ≡ I.
Proof.
  intros.
  rewrite intComp_comm.
  now apply intComp_unit.
Qed.

(* The components of valid composite interfaces are valid. *)
Lemma intComp_valid_proj1 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.
Proof.
  intros I1 I2.
  rewrite <- Decidable.contrapositive.
  apply intComp_invalid.
  unfold Decidable.decidable.
  generalize (flowint_valid_dec I1).
  unfold Decision.
  intros.
  destruct H0.
  all: auto.
Qed.

Lemma intComp_valid_proj2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I2.
Proof.
  intros I1 I2.
  rewrite intComp_comm.
  apply intComp_valid_proj1.
Qed.

(* If a composite interface is empty then its components must have been empty. *)
Lemma intComp_positive_1 : ∀ (I1 I2: flowintT), I1 ⋅ I2 = ∅ → I1 = ∅.
Proof.
  intros ? ? C.
  pose proof intEmp_valid as V.
  unfold empty, flowint_empty in C.
  rewrite <- C in V.
  pose proof (intComp_valid_proj1 _ _ V) as V1.
  pose proof (intComp_valid_proj2 _ _ V) as V2.
  assert (inf_map I1 = ∅) as D1.
  apply map_eq.
  intros n.
  assert (inf_map (I1 ⋅ I2) !! n = inf_map (I_empty) !! n) as CL.
    by rewrite C; reflexivity.
  unfold op, intComp in CL.
  unfold op, intComp in C.
  destruct (decide (intComposable I1 I2)).
  - unfold inf_map at 1 in CL. simpl in CL.
    rewrite gmap_imerge_prf in CL.
    rewrite lookup_empty.
    rewrite lookup_empty in CL.
    destruct (inf_map I1 !! n);
      destruct (inf_map I2 !! n);
      inversion CL.
    reflexivity.
  - destruct (decide (I1 = ∅)).
    * rewrite e.
      unfold inf_map, empty at 1, flowint_empty, I_empty, I_emptyR.
      simpl.
      reflexivity.
    * destruct (decide (I2 = ∅)).
      + unfold empty, flowint_empty in n1.
        contradiction.
      + unfold I_empty in C.
        inversion C.
  - assert (domm I1 ≡ ∅).
    unfold domm, dom, flowint_dom.
    rewrite D1.
    rewrite dom_empty.
    reflexivity.
    pose proof (intEmp_unique _ V1 H0).
    trivial.
Qed.

Lemma intComp_positive_2 : ∀ (I1 I2: flowintT), I1 ⋅ I2 = ∅ → I2 = ∅.
Proof.
  intros ? ? C.
  rewrite intComp_comm in C *.
  apply intComp_positive_1.
Qed.

(* The empty interface is composable with any valid interface. *)
Lemma intComposable_empty : ∀ I: flowintT, ✓ I → intComposable ∅ I.
Proof.
  intros I IV.
  case_eq I; last first.
  intros.
  rewrite H0 in IV.
  unfold valid, flowint_valid in IV.
  contradiction.
  intros Ir Idef.
  rewrite <- Idef.
  unfold intComposable.
  repeat split.
  - trivial.
  - unfold domm, dom, flowint_dom, inf_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite dom_empty.
    apply disjoint_empty_l.
  - unfold map_Forall.
    intros n x.
    unfold inf_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite lookup_empty.
    intros.
    inversion H0.
  - unfold map_Forall.
    intros n x.
    intros.
    unfold out, out_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite nzmap_lookup_empty.
    rewrite ccm_left_id.
    rewrite ccm_pinv_unit.
    unfold inf.
    rewrite H0.
    auto.
Qed.

(* The components of valid composite interfaces are composable. *)
Lemma intComposable_valid : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → intComposable I1 I2.
Proof.
  intros I1 I2 IV.
  pose proof (intComp_valid_proj1 I1 I2 IV) as I1V.
  pose proof (intComp_valid_proj2 I1 I2 IV) as I2V.
  case_eq (I1 ⋅ I2).
  - intros Ir Idef.
    unfold op, intComp in Idef.
    destruct (decide (intComposable I1 I2)).
    trivial.
    destruct (decide (I1 = ∅)).
    pose proof (intComposable_empty I2).
    apply H0 in I2V.
    rewrite e.
    trivial.
    destruct (decide (I2 = ∅)).
    pose proof (intComposable_empty I1).
    apply H0 in I1V.
    rewrite intComposable_comm.
    rewrite e.
    trivial.
    inversion Idef.
  - intros.
    rewrite H0 in IV.
    unfold valid, flowint_valid in IV.
    contradiction.
Qed.

(* The composition of composable interfaces is valid. *)
Lemma intValid_composable : ∀ (I1 I2: flowintT), intComposable I1 I2 → ✓ (I1 ⋅ I2).
Proof.
  intros ? ? V.
  unfold op, intComp.
  destruct (decide (intComposable I1 I2)).
  unfold valid, flowint_valid.
  simpl.
  split.

  - assert (dom (gset Node) (infComp I1 I2) ## dom (gset Node) (nzmap_car (outComp I1 I2))).
    { apply elem_of_disjoint.
      intros n Hin Hout.
      rewrite infComp_dom in Hin.
      rewrite nzmap_elem_of_dom_total in Hout *.
      intros.
      unfold outComp in H0.
      rewrite nzmap_lookup_imerge in H0.
      unfold outComp_op in H0.
      destruct (decide _).
      all: contradiction.
    }
    apply map_disjoint_dom in H0.
    trivial.
  
  - intros.
    assert (dom (gset Node) (infComp I1 I2) ≡ dom (gset Node) (∅ : gmap Node flowdom)).
    rewrite H0. auto.
    apply nzmap_eq.
    intros n.
    unfold outComp.
    rewrite nzmap_lookup_imerge.
    unfold outComp_op.
    rewrite nzmap_lookup_empty.
    rewrite infComp_dom in H1.
    rewrite dom_empty in H1 *.
    intros.
    destruct (decide _). auto.
    assert (domm I1 ≡ ∅) by set_solver.
    assert (domm I2 ≡ ∅) by set_solver.
    destruct V as (V1 & V2 & _).
    unfold valid, flowint_valid in V1,V2.
    destruct I1 as [Ir1|], I2 as [Ir2|].
    destruct V1 as (_ & E1).
    destruct V2 as (_ & E2).
    unfold domm, dom, flowint_dom, inf_map in H2, H3.
    apply dom_empty_inv in H2.
    apply dom_empty_inv in H3.
    apply E1 in H2.
    apply E2 in H3.
    unfold out_map.
    rewrite H2.
    rewrite H3.
    rewrite nzmap_lookup_empty.
      by rewrite ccm_right_id.
      all: contradiction.
  - contradiction.
Qed.

(* Characterization of inflows of composite interfaces. *)
Lemma intComp_unfold_inf_1 : ∀ (I1 I2: flowintT),
    ✓ (I1 ⋅ I2) →
    ∀ n, n ∈ domm I1 → inf I1 n = inf (I1 ⋅ I2) n + out I2 n.
Proof.
  intros I1 I2 V n D.
  unfold domm, dom, flowint_dom in D.
  apply elem_of_dom in D.
  unfold is_Some in D.
  destruct D as [x D].
  pose proof (intComposable_valid I1 I2 V).
  assert (IC := H0).
  unfold intComposable in H0.
  destruct H0 as (I1v & I2v & Disjoint & I1inf & I2inf).
  unfold map_Forall in I1inf.
  pose proof (I1inf n (inf I1 n)).
  unfold inf in H0.
  rewrite D in H0.
  unfold default, id in H0.
  assert (Some x = Some x) by reflexivity.
  apply H0 in H1.
  unfold valid, flowint_valid in V.
  case_eq (I1 ⋅ I2).
  - intros Ir Idef. rewrite Idef in V.
    unfold op, intComp in Idef.
    destruct (decide (intComposable I1 I2)).
    + unfold inf.
      rewrite <- Idef.
      unfold inf_map at 1; simpl.
      rewrite gmap_imerge_prf.
      * rewrite D.
        unfold default, id.
        rewrite ccm_comm in H1.
        trivial.
    + contradiction.
  - intros.
    rewrite H2 in V.
    contradiction.
Qed.

Lemma intComp_unfold_inf_2 : ∀ (I1 I2: flowintT),
    ✓ (I1 ⋅ I2) →
    ∀ n, n ∈ domm I2 → inf I2 n = inf (I1 ⋅ I2) n + out I1 n.
Proof.
  intros.
  rewrite intComp_comm.
  apply intComp_unfold_inf_1.
  rewrite intComp_comm.
  trivial.
  exact H1.
Qed.

(* Characterization of outflow of composed interfaces. *)
Lemma intComp_unfold_out I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∉ domm (I1 ⋅ I2) → out (I1 ⋅ I2) n = out I1 n + out I2 n).
Proof.
  intros.
  apply intComp_dom in H0 as D.
  rewrite D in H1.
  pose proof (outComp_inv I1 I2 n H1).
  apply intComposable_valid in H0.
  unfold op, intComp, out at 1, out_map at 1.
  destruct (decide (intComposable I1 I2)); last first.
  contradiction.
  simpl.
  trivial.
Qed.

(* Characterization of inflow of composed interfaces. *)
Lemma intComp_inf_1 I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∈ domm I1 → inf (I1 ⋅ I2) n = inf I1 n - out I2 n).
Proof.
  intros V n D.
  apply intComposable_valid in V.
  unfold op, intComp.
  destruct (decide (intComposable I1 I2)); last first.
  contradiction.
  unfold inf at 1, inf_map at 1.
  simpl.
  rewrite gmap_imerge_prf.
  unfold domm, dom, flowint_dom in D.
  apply elem_of_dom in D.
  unfold is_Some in D.
  destruct D as [x D].
  unfold inf at 1.
  rewrite D.
  simpl.
  reflexivity.
Qed.

Lemma intComp_inf_2 I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∈ domm I2 → inf (I1 ⋅ I2) n = inf I2 n - out I1 n).
Proof.
  intros.
  rewrite intComp_comm.
  generalize H1.
  generalize n.
  rewrite intComp_comm in H0 *.
  apply intComp_inf_1.
Qed.


(* Characterization of interface composition as defined in ESOP'20. *)
Lemma intComp_fold I1 I2 I :
  I ≠ intUndef → ✓ I1 → ✓ I2 →
  domm I1 ## domm I2 →
  domm I = domm I1 ∪ domm I2 →
  (∀ n, n ∈ domm I1 → inf I1 n = out I2 n + inf I n) →
  (∀ n, n ∈ domm I2 → inf I2 n = out I1 n + inf I n) →
  out_map I = outComp I1 I2 →
  I = I1 ⋅ I2 ∧ ✓ (I1 ⋅ I2).
Proof.
  intros Iint V1 V2 Disj D Inf1 Inf2 Out.
  assert (intComposable I1 I2) as C.
  { unfold intComposable.
    repeat split; try trivial.
    - unfold map_Forall.
      intros n x xDef.
      unfold domm, dom, flowint_dom in Inf1.
      pose proof (Inf1 n).
      rewrite elem_of_dom in H0 *.
      intro.
      apply mk_is_Some in xDef as H1.
      apply H0 in H1.
      rewrite H1.
      rewrite (ccm_comm _ (inf I n)).
      rewrite ccm_pinv.
      unfold inf at 1 in H1.
      rewrite xDef in H1.
      simpl in H1.
      rewrite H1.
      reflexivity.
    - unfold map_Forall.
      intros n x xDef.
      unfold domm, dom, flowint_dom in Inf2.
      pose proof (Inf2 n).
      rewrite elem_of_dom in H0 *.
      intro.
      apply mk_is_Some in xDef as H1.
      apply H0 in H1.
      rewrite H1.
      rewrite (ccm_comm _ (inf I n)).
      rewrite ccm_pinv.
      unfold inf at 1 in H1.
      rewrite xDef in H1.
      simpl in H1.
      rewrite H1.
      reflexivity.
  }
  split.
  apply intValid_composable in C.
  destruct I as [Ir |].
  unfold op, intComp, infComp, infComp_op.
  destruct (decide (intComposable I1 I2)).
  f_equal.
  case_eq Ir.
  intros.
  f_equal.
  - apply map_eq.
    intros n.
    rewrite gmap_imerge_prf.
    case_eq (inf_map I1 !! n).
    + intros x xDef.
      assert (n ∈ domm I1) as nI1.
      apply mk_is_Some in xDef.
      unfold domm, dom, flowint_dom.
      apply elem_of_dom.
      trivial.
      assert (n ∈ domm (int Ir)) as nI.
      set_solver.
      unfold domm, dom, flowint_dom in nI.
      apply elem_of_dom in nI.
      unfold is_Some in nI.
      destruct nI as [y nI].
      unfold inf_map in nI.
      rewrite H0 in nI.
      simpl in nI.
      rewrite nI.
      f_equal.
      pose proof (Inf1 _ nI1) as In1n.
      unfold inf in In1n.
      rewrite xDef in In1n.
      simpl in In1n.
      rewrite ccm_comm in In1n.
      rewrite In1n.
      rewrite H0.
      simpl.
      rewrite nI.
      rewrite ccm_pinv.
      auto.
    + intros.
      assert (n ∉ domm I1).
      unfold domm, dom, flowint_dom.
      rewrite elem_of_dom.
      rewrite H1.
      apply is_Some_None.
      case_eq (inf_map I2 !! n).
      * intros x xDef.
        assert (n ∈ domm I2) as nI2.
        apply mk_is_Some in xDef.
        unfold domm, dom, flowint_dom.
        apply elem_of_dom.
        trivial.
        assert (n ∈ domm (int Ir)) as nI.
        set_solver.
        unfold domm, dom, flowint_dom in nI.
        apply elem_of_dom in nI.
        unfold is_Some in nI.
        destruct nI as [y nI].
        unfold inf_map in nI.
        rewrite H0 in nI.
        simpl in nI.
        rewrite nI.
        f_equal.
        pose proof (Inf2 _ nI2) as In2n.
        unfold inf in In2n.
        rewrite xDef in In2n.
        simpl in In2n.
        rewrite ccm_comm in In2n.
        rewrite In2n.
        rewrite H0.
        simpl.
        rewrite nI.
        auto using ccm_pinv.
      * intros.
        assert (n ∉ domm I2).
        unfold domm, dom, flowint_dom.
        rewrite elem_of_dom.
        rewrite H3.
        apply is_Some_None.
        assert (n ∉ domm (int Ir)).
        set_solver.
        unfold domm, dom, flowint_dom, inf_map in H5.
        rewrite elem_of_dom in H5 *.
        intros.
        rewrite H0 in H5.
        simpl in H5.
        rewrite <- eq_None_not_Some in H5.
        trivial.
  - unfold out_map in Out.
    rewrite H0 in Out.
    simpl in Out.
    trivial.
  - apply intComposable_valid in C.
    contradiction.
  - contradiction.
  - apply intValid_composable in C. trivial.
Qed.

(* Interface composition is associative (valid case). *)
Lemma intComp_assoc_valid (I1 I2 I3 : flowintT) : ✓ (I1 ⋅ (I2 ⋅ I3)) → I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.
Proof.
  intros V.
  remember (I1 ⋅ (I2 ⋅ I3)) as I.
  remember (I2 ⋅ I3) as I23.
  remember (outComp I1 I2) as out12.
  remember (λ n (o1 o2 : option flowdom),
            match o1, o2 with
            | Some _, _ => Some (inf I n + out I3 n)
            | _, Some _ => Some (inf I n + out I3 n)
            | None, None => None
            end) as f_inf. 
  assert (∀ n, DiagNone (f_inf n)) as H_diag.
  { intros. unfold DiagNone. rewrite Heqf_inf. trivial. }
  remember (gmap_imerge f_inf (*(infComp_op I I3)*)
                        (inf_map I1) (inf_map I2)) as inf12.
  remember (int {| infR := inf12; outR := out12 |}) as I12.
  rewrite HeqI in V.
  apply intComp_valid_proj1 in V as V1.
  apply intComp_valid_proj2 in V as V23.
  rewrite HeqI23 in V23.
  apply intComp_valid_proj1 in V23 as V2.
  apply intComp_valid_proj2 in V23 as V3.
  apply intComposable_valid in V as C.
  apply intComposable_valid in V23 as C23.
  assert (CU := C).
  unfold intComposable in CU.
  destruct CU as (_ & _ & Disj & Inf1 & Inf23).
  assert (CU23 := C23).
  unfold intComposable in CU23.
  destruct CU23 as (_ & _ & Disj23 & Inf2 & Inf3).
  apply intComp_dom in V as D.
  apply intComp_dom in V23 as D23.
  rewrite HeqI23 in Disj.
  rewrite D23 in Disj.
  unfold map_Forall in Inf1.
  unfold map_Forall in Inf23.
  unfold map_Forall in Inf2.
  unfold map_Forall in Inf3.
  assert (I12 ≡ I1 ⋅ I2 ∧ ✓ (I1 ⋅ I2)) as I12Def.
  { apply intComp_fold.
    - rewrite HeqI12. auto.
    - trivial.
    - trivial.
    - set_solver.
    - rewrite set_eq.
      intros n.
      rewrite elem_of_union.
      split.
      * intros nD.
        unfold domm, dom, flowint_dom, inf_map in nD.
        rewrite HeqI12 in nD.
        simpl in nD.
        rewrite Heqinf12 in nD.
        rewrite elem_of_dom in nD *.
        intros nD.
        rewrite gmap_imerge_prf in nD.
        unfold domm, dom, flowint_dom.
        repeat rewrite elem_of_dom.
        destruct (inf_map I1 !! n).
        unfold is_Some.
        left.
        exists f.
        reflexivity.
        destruct (inf_map I2 !! n).
        right.
        exists f.
        reflexivity.
        rewrite Heqf_inf in nD.
        apply is_Some_None in nD.
        contradiction.
      * intros nD.
        
        unfold domm, dom, flowint_dom, inf_map.
        rewrite HeqI12.
        simpl.
        rewrite Heqinf12.
        rewrite elem_of_dom.
        rewrite gmap_imerge_prf.
        rewrite Heqf_inf.
        destruct nD as [nD | nD];
        unfold domm, dom, flowint_dom in nD;
        rewrite elem_of_dom in nD *;
        intros nD;
        unfold is_Some in nD;
        destruct nD as [x nD];
        rewrite nD;
        destruct (inf_map I1 !! n);
        apply not_eq_None_Some;
        auto.
    - intros ? n_in_I1.
      assert (n_in_I11 := n_in_I1).
      unfold domm, dom, flowint_dom in n_in_I11.
      apply elem_of_dom in n_in_I11.
      unfold is_Some in n_in_I11.
      destruct n_in_I11 as [x n_inf].
      apply Inf1 in n_inf as xDef.
      unfold inf at 2.
      rewrite HeqI12.
      unfold inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite n_inf.
      rewrite Heqf_inf.
      simpl.
      rewrite HeqI.
      pose proof (intComp_inf_1 _ _ V _ n_in_I1).
      rewrite H0.
      unfold inf at 2.
      rewrite n_inf.
      simpl.
      rewrite xDef.
      rewrite (ccm_comm (out I23 n)).
      rewrite ccm_pinv.
      rewrite ccm_comm.
      rewrite <- ccm_assoc.
      rewrite (ccm_comm (out I3 n)).
      assert (n ∉ domm (I2 ⋅ I3)).
      rewrite D23.
      set_solver.
      apply intComp_unfold_out in H1.
      unfold inf at 1.
      rewrite n_inf.
      simpl.
      rewrite xDef.
      rewrite ccm_comm.
      rewrite <- H1.
      rewrite <- HeqI23.
      reflexivity.
      trivial.
    - intros ? n_in_I2.
      assert (n_in_I21 := n_in_I2).
      unfold domm, dom, flowint_dom in n_in_I21.
      apply elem_of_dom in n_in_I21.
      unfold is_Some in n_in_I21.
      destruct n_in_I21 as [x n_inf].
      apply Inf2 in n_inf as xDef.
      unfold inf at 2.
      rewrite HeqI12.
      unfold inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite n_inf.
      rewrite Heqf_inf.
      rewrite HeqI.
      assert (n ∈ domm I2 ∪ domm I3) as n_in_I23.
      set_solver.
      rewrite <- D23 in n_in_I23.
      rewrite <- HeqI23 in n_in_I23.
      unfold inf at 2.
      assert (n ∉ domm I1) as n_nin_I1.
      set_solver.
      unfold domm, dom, flowint_dom in n_nin_I1.
      rewrite elem_of_dom in n_nin_I1 *.
      intros n_nin_I1.
      rewrite <- eq_None_not_Some in n_nin_I1.
      rewrite n_nin_I1.
      simpl.
      rewrite ccm_comm.
      rewrite <- ccm_assoc.
      rewrite (ccm_comm (out I3 n)).
      rewrite ccm_assoc.
      pose proof (intComp_unfold_inf_2 I1 I23 V n n_in_I23).
      rewrite <- H0.
      pose proof (intComp_unfold_inf_1 I2 I3 V23 n n_in_I2).
      rewrite H1.
      rewrite HeqI23.
      reflexivity.
    - rewrite HeqI12.
      unfold out_map.
      auto. }
  destruct I12Def as (I12Def & V12).
  assert (I ≡ I12 ⋅ I3) as IDef.
  { apply intComp_fold.
    - rewrite HeqI.
      destruct (I1 ⋅ I23).
      * auto.
      * apply intUndef_not_valid in V.
        contradiction.
    - rewrite <- I12Def in V12.
      trivial.
    - trivial.
    - rewrite I12Def.
      rewrite intComp_dom.
      set_solver.
      trivial.
    - rewrite I12Def.
      rewrite intComp_dom.
      rewrite HeqI.
      rewrite D.
      rewrite HeqI23.
      rewrite D23.
      set_solver.
      trivial.
    - intros n nI12.
      rewrite HeqI12.
      unfold inf at 1, inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite I12Def in nI12 *.
      intro nI12.
      rewrite intComp_dom in nI12.
      rewrite elem_of_union in nI12 *.
      intro nI12.
      destruct nI12 as [nI1 | nI2].
      * unfold domm, dom, flowint_dom in nI1.
        apply elem_of_dom in nI1.
        unfold is_Some in nI1.
        destruct nI1 as [x nI1].
        rewrite nI1.
        simpl.
        rewrite Heqf_inf.
        simpl.
        auto using ccm_comm.
      * destruct (inf_map I1 !! n).
        ** rewrite Heqf_inf. simpl.
           auto using ccm_comm.
        ** unfold domm, dom, flowint_dom in nI2.
           apply elem_of_dom in nI2.
           unfold is_Some in nI2.
           destruct nI2 as [x nI2].
           rewrite nI2.
           rewrite Heqf_inf.
           simpl.
           auto using ccm_comm.
      * trivial.
    - intros n nI3.
      assert (n ∉ domm I1 ∪ domm I2) as n_not_I12.
      set_solver.
      rewrite <- intComp_dom in n_not_I12.
      pose proof (intComp_unfold_out I1 I2 V12 n n_not_I12).
      rewrite I12Def.
      rewrite H0.
      assert (n ∈ domm I23) as nI23.
      set_solver.
      pose proof (intComp_unfold_inf_2 I1 I23 V n nI23).
      rewrite <- HeqI in H1.
      rewrite ccm_comm.
      rewrite ccm_assoc.
      rewrite <- H1.
      pose proof (intComp_unfold_inf_2 I2 I3 V23 n nI3).
      rewrite <- HeqI23 in H2.
      rewrite <- H2.
      reflexivity.
      trivial.
    - rewrite HeqI.
      unfold op, intComp.
      destruct (decide (intComposable I1 I23)); last first.
      contradiction.
      simpl.
      apply nzmap_eq.
      intros n.
      unfold outComp.
      repeat rewrite nzmap_lookup_imerge.
      unfold outComp_op.
      pose proof (intComp_unfold_out I1 I2 V12 n).
      rewrite <- I12Def in H0.
      pose proof (intComp_unfold_out I2 I3 V23 n).
      rewrite <- HeqI23 in H1.
      unfold out in H0.
      unfold out in H1.
      rewrite HeqI23.
      rewrite D23.
      assert (I12 = I1 ⋅ I2) as I12def.
      rewrite I12Def; reflexivity.
      rewrite I12def.
      pose proof (intComp_dom _ _ V12) as D12.
      rewrite D12.
      destruct (decide _), (decide _); try auto.
      set_solver. set_solver.
      rewrite not_elem_of_union in n0 *.
      rewrite not_elem_of_union in n1 *.
      intros n0 n1.
      destruct n0 as (n0 & _).
      destruct n1 as (_ & n1).
      rewrite <- D12, <- I12Def in n0.
      rewrite <- D23, <- HeqI23 in n1.
      apply H0 in n0.
      apply H1 in n1.
      rewrite <- HeqI23, <- I12Def, n0, n1.
      by rewrite ccm_assoc.
  }

  rewrite I12Def in IDef *.
  intros.
  trivial.
Qed.

(* Interface composition is associative (invalid case). *)
Lemma intComp_assoc_invalid (I1 I2 I3 : flowintT) : ¬(✓ (I1 ⋅ (I2 ⋅ I3))) → ¬(✓ (I1 ⋅ I2 ⋅ I3)) → I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.
Proof.
  intros IV1 IV2.
  pose proof (intValid_composable I1 (I2 ⋅ I3)) as NC1.
  rewrite <- Decidable.contrapositive in NC1.
  pose proof (NC1 IV1).
  pose proof (intValid_composable (I1 ⋅ I2) I3) as NC2.
  rewrite <- Decidable.contrapositive in NC2.
  pose proof (NC2 IV2).
  all: try (unfold Decidable.decidable; auto).

  destruct (decide (I1 = ∅)).
  - rewrite e.
    rewrite intComp_comm.
    rewrite intComp_unit.
    rewrite (intComp_comm _ I2).
    rewrite intComp_unit.
    reflexivity.
  - destruct (decide (I2 = ∅)).
    + rewrite e.
      rewrite (intComp_comm _ I3).
      repeat rewrite intComp_unit.
      reflexivity.
    + destruct (decide ((I1 ⋅ I2) = ∅)).
      apply intComp_positive_1 in e.
      contradiction.
      * destruct (decide ((I2 ⋅ I3) = ∅)).
        ** apply intComp_positive_1 in e.
           contradiction.
        ** destruct (decide (I3 = empty)).
           rewrite e.
           repeat rewrite intComp_unit.
           reflexivity.
           unfold op at 1, intComp at 1.
           destruct (decide (intComposable I1 (I2 ⋅ I3))).
           apply H0 in i.
           contradiction.
           unfold op at 8, intComp.
           destruct (decide (intComposable (I1 ⋅ I2) I3)).
           apply H1 in i.
           contradiction.
           destruct (decide (I1 = ∅)); try contradiction.
           destruct (decide (I2 ⋅ I3 = ∅)); try contradiction.
           destruct (decide (I1 ⋅ I2 = ∅)); try contradiction.
           destruct (decide (I3 = ∅)); try contradiction.
           reflexivity.
Qed.

(* Interface composition is associative. *)
Lemma intComp_assoc : Assoc (≡) intComp.
Proof.
  unfold Assoc.
  intros I1 I2 I3.
  destruct (decide (✓ (I1 ⋅ (I2 ⋅ I3)))).
  - apply intComp_assoc_valid in v.
    trivial.
  - destruct (decide (✓ (I1 ⋅ I2 ⋅ I3))).
    * rewrite (intComp_comm I1) in v *.
      intros v.
      rewrite (intComp_comm _ I3) in v *.
      intros v.
      apply intComp_assoc_valid in v.
      rewrite intComp_comm in v *.
      intros v.
      rewrite (intComp_comm I3) in v *.
      intros v.
      rewrite (intComp_comm I2) in v *.
      intros v.
      rewrite (intComp_comm _ I1) in v *.
      trivial.
    * apply intComp_assoc_invalid.
      all: trivial.
Qed.

(** Auxiliary definitions for setting up flow interface camera. *)

Global Instance flowintRAcore : PCore flowintT :=
  λ I, match I with
       | int Ir => Some I_empty
       | intUndef => Some intUndef
       end.

Global Instance flowintRAunit : cmra.Unit flowintT := I_empty.

Definition flowintRA_mixin : RAMixin flowintT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    eauto using intComp_assoc.
  - (* Commutativity *)
    unfold Comm. eauto using intComp_comm.
  - (* Core-ID *)
    intros x cx.
    destruct cx eqn:?; unfold pcore, flowintRAcore; destruct x eqn:?;
      try (intros H1; inversion H1).
    + rewrite intComp_comm.
      apply intComp_unit.
    + apply intComp_undef_op.
  - (* Core-Idem *)
    intros x cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x;
      try (intros H0; inversion H0); try done.
  - (* Core-Mono *)
    intros x y cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      intros H1; inversion H1; destruct y; try eauto.
    + exists I_empty. split; try done.
      exists (int I_emptyR). by rewrite intComp_unit.
    + exists intUndef. split; try done. exists intUndef.
      rewrite intComp_comm. by rewrite intComp_unit.
    + exists I_empty. split; try done.
      destruct H0 as [a H0].
      assert (intUndef ≡ intUndef ⋅ a); first by rewrite intComp_undef_op.
      rewrite <- H0 in H2.
      inversion H2.
  - (* Valid-Op *)
    intros x y. unfold valid. apply intComp_valid_proj1.
Qed.


Canonical Structure flowintRA := discreteR flowintT flowintRA_mixin.

Global Instance flowintRA_cmra_discrete : CmraDiscrete flowintRA.
Proof. apply discrete_cmra_discrete. Qed.

Global Instance flowintRA_cmra_total : CmraTotal flowintRA.
Proof.
  rewrite /CmraTotal. intros. destruct x.
  - exists I_empty. done.
  - exists intUndef. done.
Qed.

Lemma flowint_ucmra_mixin : UcmraMixin flowintT.
Proof.
  split; try apply _; try done.
  unfold ε, flowintRAunit, valid.
  unfold LeftId.
  intros I.
  rewrite intComp_comm.
  apply intComp_unit.
Qed.

End flowint.

Section cmra.

Context (flowdom: Type) `{CCM flowdom}.

Open Scope ccm_scope.

(* The unital camera of flow interfaces. *)
Canonical Structure flowintUR : ucmra := Ucmra flowintT flowint_ucmra_mixin.

(** Assorted convenience lemmas. *)

Lemma flowint_valid_defined (I: flowintUR) : ✓ I → ∃ Ir, I = int Ir.
Proof.
  intros IV.
  destruct I.
  - exists f.
    reflexivity.
  - apply intUndef_not_valid in IV.
    contradiction.
Qed.


Lemma flowint_valid_unfold (I : flowintUR) : ✓ I → ∃ Ir, I = int Ir ∧ infR Ir ##ₘ nzmap_car (outR Ir)
                                                      ∧ (infR Ir = ∅ → outR Ir = ∅).
Proof.
  intros.
  unfold valid, cmra_valid in H0.
  simpl in H0.
  unfold ucmra_valid in H0.
  simpl in H0.
  unfold flowint_valid in H0.
  destruct I.
  - exists f.
    naive_solver.
  - contradiction.
Qed.

Lemma flowint_contains I n (m: flowdom) : ✓ I →  inf_map I !! n = Some m → n ∈ domm I.
Proof.
  intros HI Hinf. unfold domm, dom. rewrite elem_of_dom. unfold is_Some. exists m. done.
Qed.

Lemma flowint_contains_not (I: flowintUR) n :  ✓ I → inf_map I !! n = None → n ∉ domm I.
Proof.
  intros HI Hinf. unfold domm, dom. rewrite elem_of_dom. unfold is_Some. unfold not.
  intros Hcon. destruct Hcon as [m Hcon]. rewrite Hinf in Hcon. inversion Hcon.
Qed.

(* Lift intComp_dom to flow interface camera. *)
Lemma flowint_comp_fp : ∀ I1 I2, ✓(I1 ⋅ I2) → domm (I1 ⋅ I2) = domm I1 ∪ domm I2.
Proof.
  apply intComp_dom.
Qed.

(* Flow interface composition is cancelable. *)
Lemma intComp_cancelable (I1 I2 I3: flowintUR) : ✓ (I1 ⋅ I2) → (I1 ⋅ I2 ≡ I1 ⋅ I3) → (I2 ≡ I3).
Proof.
  intros V12 Eq.
  assert (V13 := V12).
  rewrite Eq in V13 *.
  intros V13.
  pose proof (intComposable_valid _ _ V13) as C13.
  pose proof (intComposable_valid _ _ V12) as C12.
  pose proof (intComp_valid_proj1 _ _ V12) as V1.
  pose proof (intComp_valid_proj2 _ _ V12) as V2.
  pose proof (intComp_valid_proj2 _ _ V13) as V3.
  pose proof (flowint_valid_unfold _ V1) as [Ir1 (I1_def & Disj1 & _)].
  pose proof (flowint_valid_unfold _ V2) as [Ir2 (I2_def & Disj3 & _)].
  pose proof (flowint_valid_unfold _ V3) as [Ir3 (I3_def & Disj2 & _)].
  (*pose proof (intComp_unfold_inf_2 _ _ V12).*)
  assert (C12' := C12). 
  assert (C13' := C13). 
  destruct C12' as (_ & _ & Disj12 & Inf12 & Inf2).
  unfold map_Forall in Inf2.
  destruct C13' as (_ & _ & Disj13 & Inf13 & Inf3).
  assert (domm I2 = domm I3) as D23.
  { pose proof (intComp_dom _ _ V12).
    pose proof (intComp_dom _ _ V13).
    unfold op, cmra_op, ucmra_cmraR, ucmra_op, flowintUR in Eq.
    unfold op in H1.
    unfold op in H0.
    rewrite Eq in H0 *.
    intros H0.
    set_solver. }
  rewrite I2_def.
  rewrite I3_def.
  f_equal.
  case_eq Ir2.
  intros infR2 outR2 Ir2_def.
  case_eq Ir3.
  intros infR3 outR3 Ir3_def. 
  f_equal.
  apply map_eq.
  intros n.
  assert (inf_map (I1 ⋅ I2) !! n = inf_map (I1 ⋅ I3) !! n) as Eqinf. rewrite Eq. reflexivity.
  unfold op, cmra_op, ucmra_cmraR, flowintUR, ucmra_op, intComp, inf_map in Eqinf.
  destruct (decide (intComposable I1 I2)); last first. contradiction.
  destruct (decide (intComposable I1 I3)); last first. contradiction.
  simpl in Eqinf.
  unfold infComp, infComp_op in Eqinf.
  repeat rewrite gmap_imerge_prf in Eqinf.
  rewrite I1_def in Eqinf.
  rewrite I2_def in Eqinf.
  rewrite I3_def in Eqinf.
  unfold out at 1, out at 2, out_map in Eqinf.
  simpl in Eqinf.

  destruct (decide (n ∈ domm I1)) as [n_in_I1 | n_nin_I1].
  - assert (n ∉ domm I2) as n_nin_I2 by set_solver.
    assert (n ∉ domm I3) as n_nin_I3 by set_solver.
    unfold domm, dom, flowint_dom in n_nin_I2.
    rewrite not_elem_of_dom in n_nin_I2 *.
    intros n_nin_I2.
    unfold domm, dom, flowint_dom in n_nin_I3.
    rewrite not_elem_of_dom in n_nin_I3 *.
    intros n_nin_I3.
    rewrite I2_def in n_nin_I2.
    rewrite Ir2_def in n_nin_I2.
    simpl in n_nin_I2.
    rewrite I3_def in n_nin_I3.
    rewrite Ir3_def in n_nin_I3.
    simpl in n_nin_I3.
    rewrite n_nin_I2.
    rewrite n_nin_I3.
    reflexivity.
  - unfold domm, dom, flowint_dom in n_nin_I1.
    rewrite not_elem_of_dom in n_nin_I1 *.
    intros n_nin_I1.
    rewrite I1_def in n_nin_I1.
    rewrite n_nin_I1 in Eqinf.
    rewrite Ir2_def in Eqinf.
    rewrite Ir3_def in Eqinf.
    simpl in Eqinf.
    destruct (decide (n ∈ domm I2)) as [n_in_I2 | n_nin_I2].
    + assert (n ∈ domm I3) as n_in_I3.
      { rewrite <- D23. trivial. }
      unfold domm, dom, flowint_dom in n_in_I2, n_in_I3.
      rewrite elem_of_dom in n_in_I2 *.
      intros n_in_I2.
      rewrite elem_of_dom in n_in_I3 *.
      intros n_in_I3.
      unfold is_Some in n_in_I2, n_in_I3.
      destruct n_in_I2 as [x2 n_in_I2].
      destruct n_in_I3 as [x3 n_in_I3].
      rewrite I2_def in n_in_I2.
      rewrite Ir2_def in n_in_I2. simpl in n_in_I2.
      rewrite I3_def in n_in_I3.
      rewrite Ir3_def in n_in_I3. simpl in n_in_I3.
      rewrite n_in_I2 in Eqinf.
      rewrite n_in_I3 in Eqinf.
      pose proof (Inf2 n x2).
      rewrite I2_def in H0.
      rewrite Ir2_def in H0.
      unfold inf, inf_map in H0.
      rewrite n_in_I2 in H0.
      simpl in H0.
      rewrite H0 in n_in_I2.
      pose proof (Inf3 n x3).
      rewrite I3_def in H1.
      rewrite Ir3_def in H1.
      unfold inf, inf_map in H1.
      rewrite n_in_I3 in H1.
      simpl in H1.
      rewrite H1 in n_in_I3.
      assert (x2 - out (int Ir1) n = x3 - out (int Ir1) n) by naive_solver.
      rewrite I1_def in n_in_I2.
      rewrite I1_def in n_in_I3.
      rewrite H2 in n_in_I2.
      rewrite n_in_I3.
      rewrite n_in_I2.
      all: reflexivity.
    + assert (n ∉ domm I3) as n_nin_I3.
      { rewrite <- D23. trivial. }
      unfold domm, dom, flowint_dom in n_nin_I2, n_nin_I3.
      rewrite not_elem_of_dom in n_nin_I2 *.
      intros n_nin_I2.
      rewrite not_elem_of_dom in n_nin_I3 *.
      intros n_nin_I3.
      rewrite I2_def in n_nin_I2.
      rewrite Ir2_def in n_nin_I2. simpl in n_nin_I2.
      rewrite I3_def in n_nin_I3.
      rewrite Ir3_def in n_nin_I3. simpl in n_nin_I3.
      rewrite n_nin_I2.
      rewrite n_nin_I3.
      reflexivity.
  - apply nzmap_eq.
    intros n.
    assert (out_map (I1 ⋅ I2) ! n = out_map (I1 ⋅ I3) ! n) as Eqout.
    { rewrite Eq. reflexivity. }
    unfold op, cmra_op, ucmra_cmraR, flowintUR, ucmra_op, intComp, inf_map in Eqout.
  destruct (decide (intComposable I1 I2)); last first. contradiction.
  destruct (decide (intComposable I1 I3)); last first. contradiction.
  simpl in Eqout.
  unfold outComp in Eqout.
  repeat rewrite nzmap_lookup_imerge in Eqout.
  simpl in Eqout.
  unfold outComp_op in Eqout.
  unfold map_Forall in Inf13, Inf12, Inf3, Inf2.
  destruct (decide _), (decide _).
    + destruct (decide (n ∈ domm I1)).
      * unfold domm, dom, flowint_dom in e1.
        pose proof (intComp_inf_1 I1 I2 V12 n e1).
        pose proof (intComp_inf_1 I1 I3 V13 n e1).
        rewrite elem_of_dom in e1 *.
        intros e1.
        unfold is_Some in e1.
        destruct e1 as [x e1].
        pose proof (Inf13 _ _ e1).
        pose proof (Inf12 _ _ e1).
        rewrite <- H0 in H3.
        rewrite <- H1 in H2.
        rewrite Eq in H3 *.
        intros.
        rewrite H3 in H2.
        repeat rewrite (ccm_comm (out _ _)) in H2.
        apply ccm_cancel in H2.
        rewrite I2_def in H2.
        rewrite I3_def in H2.
        rewrite Ir2_def in H2.
        rewrite Ir3_def in H2.
        unfold out, out_map in H2.
        simpl in H2.
        by rewrite H2.
      * assert (n ∈ domm I2) by set_solver.
        assert (n ∈ domm I3) by set_solver.
        pose proof (intValid_in_dom_not_out I2 n V2 H0).
        pose proof (intValid_in_dom_not_out I3 n V3 H1).
        rewrite I2_def in H2.
        rewrite Ir2_def in H2.
        rewrite I3_def in H3.
        rewrite Ir3_def in H3.
        unfold out, out_map in H2,H3.
        simpl in H2,H3.
        rewrite H2.
        rewrite H3.
        reflexivity.
    + rewrite D23 in e. contradiction.
    + rewrite D23 in n0. contradiction.
    + apply ccm_cancel in Eqout.
      rewrite I2_def in Eqout.
      rewrite I3_def in Eqout.
      rewrite Ir2_def in Eqout.
      rewrite Ir3_def in Eqout.
      unfold out_map in Eqout.
      simpl in Eqout.
        by rewrite Eqout.
Qed.

(* Flow interfaces form a cancelable camera. *)
Instance flowint_cancelable (I: flowintUR) : Cancelable I.
Proof.
  unfold Cancelable.
  intros n I1 I2 V ?.
  pose proof (intComp_cancelable _ _ _ V H0).
  eauto.
Qed.

(** Frame-preserving updates of flow interfaces. *)

(* Contextual extension of flow interfaces. *)
Definition contextualLeq (I1 I2: flowintUR) : Prop := 
             ✓ I1 ∧ ✓ I2 ∧ domm I1 ⊆ domm I2 ∧
             (∀ (n: Node), n ∈ domm(I1) → inf I1 n = inf I2 n) ∧
             (∀ (n: Node), n ∉ domm(I2) → out I1 n = out I2 n).

(* Frame-preserving updates of contextually-extended flow interfaces. *)
Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (view_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = view_frag_proj x)
                        ∧ contextualLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.

(* Contextual extension allows frame-preserving updates. *)
Lemma flowint_update : ∀ (Io I_n I_n': flowintUR),
  contextualLeq I_n I_n' ∧ (domm I_n' ∩ domm Io = ∅) ∧ (∀ n, n ∈ domm I_n'∖domm I_n → out_map Io ! n = 0)
       → (● (I_n ⋅ Io) ⋅ ◯ I_n)  ~~>: (flowint_update_P (I_n ⋅ Io) I_n I_n').
Proof.
 intros Io In In' (conteq & Hintersect & Hcond). apply cmra_discrete_updateP. intros z.
  intros Hv. assert (Hincl := Hv). apply cmra_valid_op_l in Hincl.
  assert (● (In ⋅ Io) ⋅ ◯ In = View (Some (1%Qp, to_agree (In ⋅ Io))) In) as Hdest.
  { unfold op at 1, cmra_op. simpl. unfold view_op_instance. simpl.
    assert (ε ⋅ In = In) as H'.
    apply (ucmra_unit_left_id In). rewrite H'.
    unfold op, cmra_op. simpl. done. } rewrite Hdest in Hv.
  destruct z as [auth_z frag_z] eqn: Hz. 
  destruct auth_z as [ [q Iz] | ] eqn: Hauth_z.
  - exfalso. unfold op at 1, cmra_op in Hv; simpl in Hv. 
    unfold view_op_instance in Hv. simpl in Hv.
    unfold op at 1, cmra_op in Hv. simpl in Hv.
    unfold op at 1, cmra_op in Hv. simpl in Hv.
    unfold prod_op_instance in Hv. simpl in Hv.
    unfold valid, cmra_valid in Hv. simpl in Hv.
    unfold view_valid_instance in Hv. simpl in Hv.
    destruct Hv as [Hv _]. assert (Hv' := Hv). 
    apply cmra_valid_op_r in Hv. unfold valid, cmra_valid in Hv. simpl in Hv. 
    unfold frac_valid_instance in Hv. unfold valid, cmra_valid in Hv'. simpl in Hv'. 
    unfold frac_valid_instance in Hv'. by apply frac_full_exclusive in Hv'.
  - rename frag_z into Iz. unfold op at 1 in Hv. unfold cmra_op, view_op_instance in Hv; simpl in Hv.
    unfold view_op_instance in Hv. simpl in Hv.
    unfold op at 1, cmra_op in Hv. simpl in Hv.
    assert (View (Some (1%Qp, to_agree (In ⋅ Io))) (In ⋅ Iz) = ● (In ⋅ Io) ⋅ ◯ (In ⋅ Iz)) as H'.
    unfold op, cmra_op, view_op_instance. simpl. unfold view_op_instance; simpl.
    assert (ε ⋅ intComp In Iz = intComp In Iz) as H'. rewrite left_id. done.
    rewrite H'. unfold op, cmra_op, option_op_instance; simpl. done. 
    rewrite H' in Hv. apply (auth_both_valid_discrete (In ⋅ Io) (In ⋅ Iz)) in Hv.
    destruct Hv as [Hcompz HI]. destruct Hcompz as [Iy Hcompz].
    unfold contextualLeq in conteq. destruct conteq as (Hn & Hn' & Hsub & Hinf & Hout).
    clear H'. assert (✓ (In' ⋅ Io)) as Valid_In'Io.
    { apply intValid_composable. unfold intComposable. repeat split; try done.
      ** by apply cmra_valid_op_r in HI.
      ** set_solver.
      ** unfold map_Forall. intros n m. intros Hm. apply intComposable_valid in HI.
         unfold intComposable in HI. destruct HI as (_ & HvalidIo & Hinter & Hinf' & Hout').
         unfold map_Forall in Hinf'. destruct (decide (n ∈ domm In)).
        *** assert (He := e). apply Hinf in e. rewrite <-e. apply Hinf'. unfold inf in e.
             rewrite Hm in e. case_eq (inf_map In !! n). intros p Hp. rewrite Hp in e.
             simpl in e. rewrite e; done. intros Hp. assert (n ∉ domm In). 
             apply (flowint_contains_not In n); try done. contradiction.
         *** assert (n ∈ domm In') as H'. apply (flowint_contains In' n m); try done.
             assert (n ∈ domm In' ∖ domm In) as H''. set_solver.
             apply Hcond in H''. unfold out. rewrite H''. simpl. rewrite ccm_left_id. 
             rewrite <-(ccm_right_id (inf In' n)). rewrite ccm_pinv. unfold inf.
             rewrite Hm. simpl. done.
        ** unfold map_Forall. intros n m. intros Hm. apply intComposable_valid in HI.
           unfold intComposable in HI. destruct HI as (_ & HvalidIo & Hinter & Hinf' & Hout').
           unfold map_Forall in Hout. destruct (decide (n ∈ domm In')).
           *** assert (n ∈ domm Io). apply (flowint_contains Io n m); try done.
               assert (domm In' ∩ domm Io ≠ ∅) as H'. set_solver.
               exfalso. apply H'. set_solver.
           *** assert (Hn0 := n0). apply Hout in n0. unfold map_Forall in Hout'.
               apply Hout' in Hm. rewrite n0 in Hm. rewrite Hm. done. }               
    assert (Io = Iz ⋅ Iy) as Hozy. 
    { apply (intComp_cancelable In); try done. rewrite Hcompz.
                                     rewrite cmra_assoc. done. }
    exists (● (In'⋅Io) ⋅ ◯ In'). split; last first.
    + assert (Iz ≼ Io). exists Iy. by apply leibniz_equiv_iff. 
      unfold op at 2, cmra_op; simpl. unfold view_op_instance; simpl. 
      unfold op at 1, cmra_op; simpl. unfold op at 1; simpl.
      rewrite left_id. unfold valid, cmra_valid. simpl.
      unfold view_valid_instance. simpl. split; try done. intros n.
      exists (In' ⋅ Io). split.
      * unfold op, cmra_op; simpl; done. 
      * unfold auth_view_rel, auth_view_rel_raw.
        split; try done. exists Iy. rewrite Hozy.
        by rewrite cmra_assoc.
    + unfold flowint_update_P. 
      assert (● (In' ⋅ Io) ⋅ ◯ In' = View (Some (1%Qp, to_agree (In' ⋅ Io))) In') as H'.
      { unfold op at 1, cmra_op, view_op_instance; simpl. unfold view_op_instance. simpl.
        unfold op at 1, cmra_op. simpl. assert (ε ⋅ In' = In') as H'. by rewrite left_id.
        by rewrite H'. }
      rewrite H'. clear H'. simpl. exists (In' ⋅ Io). repeat split; try done.
      * assert (domm (In ⋅ Io) = domm In ∪ domm Io) as H'. apply intComp_dom. done.
        assert (domm (In' ⋅ Io) = domm In' ∪ domm Io) as H''. apply intComp_dom. done. 
        rewrite H' H''. set_solver.
      * intros n Hin. unfold op, cmra_op; simpl. unfold ucmra_op, intComp; simpl.
        unfold intComp, infComp. assert (HI1 := HI). apply intComposable_valid in HI1.
        destruct (decide (intComposable In Io)); try contradiction. assert (HI'1 := Valid_In'Io).
        apply intComposable_valid in HI'1. destruct (decide (intComposable In' Io)); try contradiction.
        unfold inf. unfold inf_map. simpl. repeat rewrite gmap_imerge_prf; try done.
        case_eq In. intros fIn Hfin. case_eq In'. intros fIn' Hfin'. case_eq Io. intros fIo Hfio.
        case_eq (infR fIn !! n). intros mn Hmn. case_eq (infR fIn' !! n). intros mn' Hmn'.
        simpl. assert (n ∈ domm In) as n_in_In. apply (flowint_contains In n mn); try done. rewrite Hfin. simpl.
        by rewrite Hmn. assert (mn = mn') as Eq_mn. assert (inf In n = inf In' n) as Eq_infIn.
        apply Hinf; done. unfold inf, inf_map in Eq_infIn. rewrite Hfin Hfin' in Eq_infIn.
        rewrite Hmn Hmn' in Eq_infIn. by simpl in Eq_infIn. by rewrite Eq_mn.
        intros Hmn'. assert (n ∉ domm In') as n_notin_In'.
        apply (flowint_contains_not In' n); try done.
        rewrite Hfin'. simpl. by rewrite Hmn'.
        exfalso. assert (n ∈ domm In) as n_in_In. apply (flowint_contains In n mn); try done. rewrite Hfin. simpl.
        by rewrite Hmn. apply n_notin_In'. set_solver.
        intros Hfinn. case_eq (infR fIn' !! n). intros mn' Hfinn'.
        case_eq (infR fIo !! n). intros mo Hmo. assert (n ∈ domm In').
        apply (flowint_contains In' n mn'); try done. rewrite Hfin'. simpl. by rewrite Hfinn'. 
        assert (n ∈ domm Io). apply (flowint_contains Io n mo); try done. by apply cmra_valid_op_r in HI.
        rewrite Hfio. simpl. by rewrite Hmo.
        assert (domm In' ∩ domm Io ≠ ∅). set_solver. contradiction.
        intros Hfion. assert (n ∉ domm In). apply (flowint_contains_not In n); try done. rewrite Hfin. simpl.
        by rewrite Hfinn. assert (n ∉ domm Io). apply (flowint_contains_not Io n); try done.
        by apply cmra_valid_op_r in HI. rewrite Hfio. simpl. by rewrite Hfion. 
        assert (domm (In ⋅ Io) = domm In ∪ domm Io) as H'. apply intComp_dom. done.
        rewrite H' in Hin. assert (n ∉ domm In ∪ domm Io). set_solver. contradiction.
        intros Hfinn'. case_eq (infR fIo !! n). intros mo Hmo. simpl. 
        assert (n ∉ domm In') as n_notin_In'.
        apply (flowint_contains_not In' n); try done. rewrite Hfin'. simpl. by rewrite Hfinn'.
        apply Hout in n_notin_In'. rewrite <-Hfin. rewrite <-Hfin'.
        by rewrite n_notin_In'. by intros Hfion.
        intros Hio. apply cmra_valid_op_r in HI. rewrite Hio in HI. unfold valid in HI.
        rewrite /(cmra_valid flowintUR) /= in HI. rewrite /(ucmra_valid flowintUR) /= in HI.
        exfalso; done. intros Hfin'. apply cmra_valid_op_l in Valid_In'Io.
        by rewrite Hfin' in Valid_In'Io. 
        intros Hfin. by rewrite Hfin in Hn.
      * intros n Hnot. unfold op, cmra_op; simpl. unfold ucmra_op; simpl.
        unfold intComp. assert (HI1 := HI). apply intComposable_valid in HI1.
        destruct (decide (intComposable In Io)); try contradiction. assert (HI'1 := Valid_In'Io).
        apply intComposable_valid in HI'1. destruct (decide (intComposable In' Io)); try contradiction.
        unfold out, out_map. simpl. unfold outComp. repeat rewrite nzmap_lookup_imerge; try done.
        unfold outComp_op.
        rewrite intComp_dom in Hnot; try trivial.
        repeat destruct (decide _); try done.
        set_solver.
        assert (n ∉ domm In') as H'. set_solver.
        pose proof (Hout n H') as H''.
        unfold out in H''.
        by rewrite H''.
      * exists Io. split; try done.
Qed.

Close Scope ccm_scope.

End cmra.

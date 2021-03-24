Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm.
Require Import Coq.Setoids.Setoid.

(** Flow interface cameras and auxiliary lemmas for multiset flows *)

Section multiset_flows.

Context `{Countable K}.

(** CCM of finite multisets over a countable set K *)

Definition K_multiset := nzmap K nat.

Global Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := dom (gset K) m.

Global Canonical Structure multiset_flowint_ur : ucmra := flowintUR K_multiset.

Implicit Type I : multiset_flowint_ur.

(** Insets and outsets of flow interfaces *)

Definition inset I n := dom_ms (inf I n).

Definition outset I n := dom_ms (out I n).

Definition in_inset k I n := k ∈ dom_ms (inf I n).

Definition in_outset k I n := k ∈ dom_ms (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition closed I := ∀ k n, k ∉ outset I n.

(** Assorted lemmas for multiset flow interfaces *)

Lemma composable_outflow_leq_inflow I1 I2 k n :
  n ∈ domm I2 →
  intComposable I1 I2 →
  out I1 n ! k ≤ inf I2 n ! k.
Proof.
  intros Hn_in_I2 HiC.
  unfold intComposable in HiC.
  destruct HiC as (_ & _ & _ & Hinf1 & Hinf2).
  unfold map_Forall in Hinf1.
  unfold map_Forall in Hinf2.
  pose proof (Hinf2 n (inf I2 n)).
  rewrite H0.
  unfold ccmop, ccm_op, lift_op.
  simpl. unfold lift_op.
  rewrite nzmap_lookup_merge.
  unfold ccmop, ccm_op, nat_ccm, nat_op.
  lia.
  unfold domm, dom, flowint_dom in Hn_in_I2.
  apply elem_of_dom in Hn_in_I2.
  unfold is_Some in Hn_in_I2.
  destruct Hn_in_I2.
  unfold inf.
  rewrite H1. auto.
Qed.
  
Lemma inset_monotone : ∀ I I1 I2 k n,
    ✓ I → I = I1 ⋅ I2 → k ∈ inset I n → n ∈ domm I1 → k ∈ inset I1 n.
Proof.
  intros ? ? ? ? ? VI ID Inset Dom.
  rewrite ID in VI.
  pose proof (intComp_unfold_inf_1 I1 I2 VI n) as Inf1.
  apply Inf1 in Dom.
  assert (Inset1 := Inset).
  unfold inset, dom_ms, nzmap_dom in Inset.
  rewrite nzmap_elem_of_dom in Inset *.
  intros Inset.
  unfold inf, inf_map in Dom.
  pose proof (intComp_valid_proj1 I1 I2 VI) as VI1.
  apply flowint_valid_defined in VI1.
  destruct VI1 as [I1r I1D].
  pose proof (intComp_valid_proj2 I1 I2 VI) as VI2.
  apply flowint_valid_defined in VI2.
  destruct VI2 as [I2r I2D].

  apply flowint_valid_defined in VI.
  destruct VI as [I12r I12D].

  rewrite I1D in Dom.
  rewrite I1D in I12D.
  rewrite I12D in Dom.

  unfold inset, inf, dom_ms, inf_map.
  rewrite I1D.
  rewrite Dom.
  rewrite nzmap_elem_of_dom_total.
  rewrite lookup_op.
  unfold nzmap_total_lookup.
  unfold inf, is_Some, inf_map in Inset.
  destruct Inset as [x Inset].
  rewrite ID in Inset.
  rewrite I1D in Inset.
  rewrite I12D in Inset.
  rewrite Inset.
  simpl.
  
  assert (x <> 0).
  unfold inset, dom_ms in Inset1.
  rewrite nzmap_elem_of_dom_total in Inset1 *.
  intros xDef.
  rewrite ID in xDef.
  rewrite I1D in xDef.
  rewrite I12D in xDef.
  unfold inf, inf_map in xDef.
  unfold nzmap_total_lookup in xDef.
  rewrite Inset in xDef.
  simpl in xDef.
  trivial.
  
  unfold ccmop, ccm_op, nat_ccm, nat_op, out, out_map.
  unfold ccmunit, nat_unit.
  lia.
  all: apply K_multiset_ccm.
Qed.

Lemma intComp_out_zero I1 I2 n : 
        ✓ (I1 ⋅ I2) → n ∉ domm (I1 ⋅ I2) → out (I1 ⋅ I2) n = 0%CCM → out I2 n = 0%CCM.
Proof.
  intros Hvld Hn Hout. apply nzmap_eq. intros k.       
  assert (out (I1 ⋅ I2) n = (out (I1) n) + (out I2 n))%CCM.
  { apply intComp_unfold_out; try done. }
  assert (out (I1 ⋅ I2) n ! k = (out (I1) n) ! k + (out I2 n) ! k)%CCM.
  { rewrite H0. by rewrite lookup_op. }
  rewrite Hout in H1. rewrite nzmap_lookup_empty in H1.
  unfold ccmunit,ccm_unit in H1. simpl in H1.
  unfold nat_unit in H1. unfold ccmop, nat_op in H1.
  assert (out I2 n ! k = 0). lia.
  rewrite H2. rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit. 
  simpl. by unfold nat_unit.
Qed. 

Lemma flowint_step :
  ∀ I I1 I2 k n,
    ✓ I →
    closed I →
    I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ domm I2.
Proof.
  intros I I1 I2 k n vI cI dI kOut.
  rewrite dI in vI.
  
  assert (domm I = domm I1 ∪ domm I2) as disj.
  pose proof (intComp_dom _ _ vI).
  rewrite dI.
  trivial.

  (* First, prove n ∉ domm I1 *)
  destruct (decide (n ∈ domm I1)).
  pose proof (intComp_valid_proj1 I1 I2 vI) as vI1.
  pose proof (intValid_in_dom_not_out I1 n vI1 e).
  unfold outset, dom_ms in kOut.
  rewrite nzmap_elem_of_dom_total in kOut *.
  intros.
  unfold ccmunit, ccm_unit, K_multiset_ccm, lift_ccm, lift_unit in H0.
  rewrite H0 in H1.
  rewrite nzmap_lookup_empty in H1.
  contradiction.
    
  (* Now, prove n ∈ domm I *)    
  assert (n ∈ domm (I1 ⋅ I2)) as in_Inf_n.
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ domm (I1 ⋅ I2))).
  apply H0 in n1.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom_ms in not_k_out.
  rewrite nzmap_elem_of_dom_total in not_k_out *.
  intros not_k_out.
  apply dec_stable in not_k_out.
  unfold outset, dom_ms in kOut.
  rewrite nzmap_elem_of_dom_total in kOut *.
  intros kOut.
  assert (out I n ! k = out (I1 ⋅ I2) n ! k).
  rewrite dI. reflexivity.
  rewrite n1 in H1.
  rewrite lookup_op in H1.
  unfold ccmop, ccm_op in H1.
  unfold K_multiset_ccm,ccmunit,ccm_unit,nat_ccm,nat_unit,nat_op in kOut, not_k_out, H1.
  lia.
  apply dec_stable in n1. trivial.
    
  (* Finally, prove n ∈ domm I2 *)
  apply intComp_dom in vI.
  rewrite vI in in_Inf_n.
  set_solver.
Qed.

Lemma outset_distinct : ∀ I n, ✓ I ∧ (∃ k, k ∈ outset I n) → n ∉ domm I.
Proof.
  intros.
  destruct H0 as (VI & Out).
  destruct Out as [k Out].

  apply flowint_valid_unfold in VI.
  destruct VI as (Ir & dI & disj & _).

  rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in disj *.
  intros disj.

  unfold outset, dom_ms, nzmap_dom, out, out_map in Out.
  rewrite dI in Out.
  rewrite nzmap_elem_of_dom_total in Out *.
  intros Out.
  destruct (decide (outR Ir ! n = ∅)).
  rewrite e in Out.
  rewrite nzmap_lookup_empty in Out.
  contradiction.
  rewrite <- nzmap_elem_of_dom_total in n0.
  unfold dom, nzmap_dom in n0.
  
  unfold domm, dom, flowint_dom, inf_map.
  rewrite dI.
  set_solver.
Qed.

Lemma flowint_inset_step : ∀ I1 I2 k n,
    ✓ (I1 ⋅ I2) → n ∈ domm I2 → k ∈ outset I1 n → k ∈ inset I2 n.
Proof.
  intros ? ? ? ? I12V Out Inset.
  apply intComposable_valid in I12V.
  pose proof (composable_outflow_leq_inflow I1 I2 k n Out I12V).
  unfold outset, dom_ms in Inset.
  rewrite nzmap_elem_of_dom_total in Inset *; intros Inset.
  unfold inset, dom_ms.
  rewrite nzmap_elem_of_dom_total.
  unfold ccmunit, ccm_unit, nat_ccm, nat_unit in Inset.
  unfold ccmunit, ccm_unit, nat_ccm, nat_unit.
  assert (out I1 n ! k > 0 ∨ out I1 n ! k = 0). lia.
  destruct H1.
  assert (inf I2 n ! k ≠ 0). lia. trivial. contradiction.
Qed.

(** Function and lemmas for frame-preserving updates of flow interfaces *)


Definition outflow_map_set f I (n: Node) (s: gset K) : multiset_flowint_ur := 
  let I_out_n := (nzmap_map_set f s (out I n)) in
  let I'_out := (<<[n := I_out_n]>> (out_map I)) in
  (int {| infR := inf_map I ; outR := I'_out |}).

Definition inflow_map_set f I (n: Node) (s: gset K) : multiset_flowint_ur := 
  let I_inf_n := (nzmap_map_set f s (inf I n)) in
  let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
  (int {| infR := I'_inf ; outR := out_map I |}).

Lemma outflow_lookup_total_map_set f I n kt s :
      kt ∈ s → out (outflow_map_set f I n s) n ! kt = f (out I n ! kt).
Proof.
  intros Heq. unfold out.
  unfold outflow_map_set.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_map_set.
  trivial. trivial.
Qed.

Lemma outflow_lookup_total_map_set_ne f I n kt s :
      kt ∉ s → out (outflow_map_set f I n s) n ! kt = out I n ! kt.
Proof.
  intros Hneq. unfold out.
  unfold outflow_map_set.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_map_set_ne.
  trivial. trivial.
Qed.  

Lemma inflow_lookup_total_map_set f I n kt s :
      kt ∈ s → inf (inflow_map_set f I n s) n ! kt = f (inf I n ! kt).
Proof.
  intros Heq. unfold inf.
  unfold inflow_map_set.
  unfold inf. simpl.
  apply leibniz_equiv.
  rewrite lookup_partial_alter.
  simpl.
  rewrite nzmap_lookup_total_map_set.
  trivial. trivial.
Qed.

Lemma inflow_lookup_total_map_set_ne f I n kt s :
      kt ∉ s → inf (inflow_map_set f I n s) n ! kt = inf I n ! kt.
Proof.
  intros Heq. unfold inf.
  unfold inflow_map_set.
  unfold inf. simpl.
  apply leibniz_equiv.
  rewrite lookup_partial_alter.
  simpl.
  rewrite nzmap_lookup_total_map_set_ne.
  trivial. trivial.
Qed.

Lemma outflow_map_set_out_map_ne f I n S I' n' :
      n' ≠ n → I' = outflow_map_set f I n S → 
           out_map I' ! n' = out_map I ! n'.
Proof.
  intros Hneq Heq. unfold outset.
  unfold multiset_flows.dom_ms.
  replace I'.
  unfold outflow_map_set. simpl.
  rewrite nzmap_lookup_total_insert_ne.
  trivial. auto.
Qed.

Lemma outflow_map_set_outset_ne f I n S I' n' :
      n' ≠ n → I' = outflow_map_set f I n S → 
           outset I' n' = outset I n'.
Proof.
  intros Hneq Heq. unfold outset.
  unfold multiset_flows.dom_ms, out.
  rewrite (outflow_map_set_out_map_ne f I n S I' n').
  trivial. auto. auto.
Qed.
  
Lemma outflow_map_set_inf f I n S I' :
      I' = outflow_map_set f I n S →
          inf_map I' = inf_map I.
Proof.
  intros Heq.
  rewrite Heq.
  unfold outflow_map_set.
  trivial.
Qed.

Lemma inflow_map_set_ne f I n S I' n' :
      n' ≠ n → I' = inflow_map_set f I n S → 
           inf_map I' !! n' = inf_map I !! n'.
Proof.
  intros Hneq Heq. unfold inset.
  unfold multiset_flows.dom_ms.
  replace I'. 
  unfold inf. simpl.
  rewrite lookup_partial_alter_ne.
  auto. auto.
Qed.

Lemma inflow_map_set_out_eq f I n S I' :
      I' = inflow_map_set f I n S →
          out_map I' = out_map I.
Proof.
  intros Heq.
  rewrite Heq.
  unfold inflow_map_set.
  unfold outset.
  unfold inf.
  simpl.
  trivial.
Qed.

Lemma inflow_map_set_outset_ne f I n S I' n' :
      I' = inflow_map_set f I n S → 
           outset I' n' = outset I n'.
Proof.
  intros Heq.
  unfold outset.
  rewrite Heq.
  pose proof (inflow_map_set_out_eq f I n S I').
  rewrite <- Heq.
  apply H0 in Heq.
  unfold out.
  by rewrite Heq.
Qed.

Definition nzmap_decrement (k: K) (m : nzmap K nat) :=
  nzmap_map (λ n, n - 1) k m.

Definition nzmap_increment (k: K) (m : nzmap K nat) :=
  nzmap_map (λ n, n - 1) k m.

Definition nzmap_decrement_set (s: gset K) (m : nzmap K nat) : nzmap K nat := nzmap_map_set (λ n, n - 1) s m.

Definition nzmap_increment_set (s: gset K) (m : nzmap K nat) : nzmap K nat := nzmap_map_set (λ n, n + 1) s m.


Definition outflow_insert_set I (n: Node) (s: gset K) : multiset_flowint_ur :=
  outflow_map_set (λ n, n + 1) I n s.

Definition outflow_delete_set I (n: Node) (s: gset K) : multiset_flowint_ur := 
  outflow_map_set (λ n, n - 1) I n s.

(* assumes: n ∈ domm I *)           
Definition inflow_insert_set I (n: Node) (s: gset K) : multiset_flowint_ur :=
  inflow_map_set (λ n, n + 1) I n s.

(* assumes: n ∈ domm I *)
Definition inflow_delete_set I (n: Node) (s: gset K) : multiset_flowint_ur := 
  inflow_map_set (λ n, n - 1) I n s.

Lemma outflow_insert_set_outset I n S I' :
      I' = outflow_insert_set I n S → 
           outset I' n = (outset I n) ∪ S.
Proof.
  intros Heq. unfold outset.
  unfold multiset_flows.dom_ms.
  replace I'. unfold outflow_insert_set.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_map_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_map_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.

Lemma outflow_delete_set_outset I n S I' :
      (∀ k, k ∈ S → out I n ! k ≤ 1) →
        I' = outflow_delete_set I n S → 
           outset I' n = (outset I n) ∖ S.
Proof.
  intros Hkb Heq. unfold outset.
  unfold multiset_flows.dom_ms.
  replace I'. unfold outflow_delete_set.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - intros. apply Hkb in e as HxB.
    rewrite nzmap_lookup_total_map_set in H0.
    unfold ccmunit, ccm_unit, nat_ccm, nat_unit in H0. simpl.
    assert (out I n ! x - 1 = 0). lia.
    contradiction. done.
  - intros. set_solver.
  - intros. rewrite nzmap_lookup_total_map_set_ne in H0.
    rewrite elem_of_difference.
    split.
    rewrite nzmap_elem_of_dom_total.
    unfold out in H0.
    all: done.
  - intros. rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_difference in H0 *; intros.
    destruct H0 as [H0 _].
    rewrite nzmap_elem_of_dom_total in H0 *; intros.
    unfold out. all: done.
Qed.    

Lemma outflow_insert_set_outset_ne I n S I' n' :
      n' ≠ n → I' = outflow_insert_set I n S → 
           outset I' n' = outset I n'.
Proof.
  apply outflow_map_set_outset_ne.
Qed.

Lemma outflow_delete_set_outset_ne I n S I' n' :
      n' ≠ n → I' = outflow_delete_set I n S → 
           outset I' n' = outset I n'.
Proof.
  apply outflow_map_set_outset_ne.
Qed.


Lemma inflow_insert_set_out_eq I n S I' n' :
      I' = inflow_insert_set I n S →
          out I' n' = out I n'.
Proof.
  unfold out.
  intros.
  rewrite (inflow_map_set_out_eq (λ n, n + 1) I n S I').
  trivial. trivial.
Qed.

Lemma inflow_insert_set_outset_ne I n S I' n' :
      I' = inflow_insert_set I n S → 
           outset I' n' = outset I n'.
Proof.
  apply inflow_map_set_outset_ne.
Qed.

Lemma outflow_insert_set_inset I n S I' n' :
      I' = outflow_insert_set I n S → 
          inset I' n' = inset I n'.
Proof.
  unfold inset.
  pose proof (outflow_map_set_inf (λ n, n + 1) I n S I').
  unfold outflow_insert_set.
  intros.
  unfold inf.
  rewrite H0. auto. auto.
Qed.


Lemma inflow_insert_set_inset_ne I n S I' n' :
      n' ≠ n → I' = inflow_insert_set I n S → 
           inset I' n' = inset I n'.
Proof.
  unfold inset.
  pose proof (inflow_map_set_ne (λ n, n + 1) I n S I' n').
  intros.
  unfold inf.
  rewrite H0; done.
Qed.

Lemma flowint_outflow_map_set_dom f I n S I' :
  I' = outflow_map_set f I n S →
  (dom (gset Node) (out_map I') ⊆ dom _ (out_map I) ∪ {[n]}).
Proof.
  intros Heq.
  apply elem_of_subseteq.
  intros n' HinI'.
  apply elem_of_union.
  destruct (decide (n = n')).
  - set_solver.
  - left.
    replace I' in HinI'.
    unfold outflow_map_set, out_map at 1 in HinI'. simpl in HinI'.
    apply nzmap_elem_of_dom_total in HinI'.
    rewrite nzmap_lookup_total_insert_ne in HinI'.
    rewrite nzmap_elem_of_dom_total.
    trivial.
    trivial.
Qed.    

Lemma flowint_inflow_map_set_dom f (I: multiset_flowint_ur) n S I':
    I' = inflow_map_set f I n S
    → domm I' = domm I ∪ {[n]}.
Proof.
  intros Heq.
  unfold domm, dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne f I n S I' n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      rewrite Heq.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.      

Lemma flowint_outflow_map_set_domm f (I: multiset_flowint_ur) n S I':
    I' = outflow_map_set f I n S
    → domm I' = domm I.
Proof.
  intros Heq.
  replace I'.
  unfold outflow_map_set.
  unfold domm, dom, flowint_dom. trivial.
Qed.

Lemma flowint_map_set_infComp f I1 I1' I2 I2' n S :
      (∀ k, k ∈ S → (inf I2 n ! k) - (out I1 n ! k) = f (inf I2 n ! k) - f (out I1 n ! k)) →
      n ∈ domm I2 → 
        I1' = outflow_map_set f I1 n S →
        I2' = inflow_map_set f I2 n S →
          infComp I1 I2 = infComp I1' I2'.
Proof.
  intros Hf n_in_I2 Hi1 Hi2. apply map_eq.
  intros n'. unfold infComp. rewrite !gmap_imerge_prf.
  unfold infComp_op.
  destruct (decide (n' = n)).
  - replace n'.
    assert (inf_map I1 !! n = inf_map I1' !! n) as Hin_eq.
    { replace I1'. unfold inf_map. by simpl. }
    assert (out I2 n = out I2' n) as Hon_eq.
    { replace I2'. unfold inflow_insert_set.
      unfold out, out_map. by simpl. }  
    destruct (inf_map I1 !! n) as [i1 | ] eqn: Hi1n.
    + rewrite Hon_eq.
      destruct (inf_map I1' !! n); by inversion Hin_eq.
    + destruct (inf_map I1' !! n); inversion Hin_eq.
      destruct (inf_map I2 !! n) as [i2 | ] eqn: Hi2n.
      * replace I2'. simpl. rewrite lookup_insert.
        apply f_equal.
        unfold inf. rewrite Hi2n. simpl.
        replace I1'. unfold inflow_insert_set. 
        unfold out, out_map at 2. simpl.
        rewrite nzmap_lookup_total_insert.
        unfold ccmop_inv, ccm_opinv.
        simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv.
        simpl. unfold nat_opinv.
        apply nzmap_eq. intros k.
        rewrite !nzmap_lookup_merge.
        destruct (decide (k ∈ S)).
        ** rewrite !nzmap_lookup_total_map_set.
           pose proof Hf k e0.
           unfold inf, out at 1 in H0.
           rewrite Hi2n in H0. simpl in H0.
           apply H0. all: done.
        ** rewrite !nzmap_lookup_total_map_set_ne; try done.
      * unfold domm, dom, flowint_dom in n_in_I2.
        rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
        rewrite Hi2n in n_in_I2. exfalso. 
        destruct n_in_I2 as [x n_in_I2]. 
        inversion n_in_I2. 
  - assert (inf_map I1 !! n' = inf_map I1' !! n') as Eq1.
    { replace I1'. unfold outflow_insert_set.
      unfold inf_map at 2. by simpl. }
    assert (out I2 n' = out I2' n') as Eq2.
    { replace I2'. unfold inflow_insert_set. 
      unfold out, out_map at 2. by simpl. }
    assert (inf_map I2 !! n' = inf_map I2' !! n') as Eq3. 
    { replace I2'. unfold inflow_insert_set.
      unfold inf_map at 2. simpl.
      rewrite lookup_insert_ne; try done. }
    assert (out I1 n' = out I1' n') as Eq4.
    { replace I1'. unfold outflow_map_set.
      unfold out, out_map at 2. simpl.
      rewrite nzmap_lookup_total_insert_ne; try done. }
    by rewrite Eq1 Eq2 Eq3 Eq4.
Qed.

Lemma flowint_map_set_outComp f I1 I1' I2 I2' n S :
      n ∈ domm I2 → 
        I1' = outflow_map_set f I1 n S →
          I2' = inflow_map_set f I2 n S →
            outComp I1 I2 = outComp I1' I2'.
Proof.
  intros n_in_I2 Hi1 Hi2. apply nzmap_eq. intros n'.
  unfold outComp. rewrite !nzmap_lookup_imerge.
  unfold outComp_op.
  pose proof (flowint_inflow_map_set_dom _ I2 n S I2' Hi2) as domm_2.
  destruct (decide (n' = n)).
  - replace n'.
    assert (n ∈ domm I2') as n_in_I2' by set_solver.
    destruct (decide (n ∈ domm I1 ∪ domm I2)); 
    last by set_solver.
    by destruct (decide (n ∈ domm I1' ∪ domm I2')); 
    last by set_solver.
  - destruct (decide (n' ∈ domm I1 ∪ domm I2)).
    + assert (n' ∈ domm I1' ∪ domm I2') as n'_in_I12' by set_solver.
      by destruct (decide (n' ∈ domm I1' ∪ domm I2')); last by set_solver.
    + assert (n' ∉ domm I1' ∪ domm I2') as n_notin_I12' by set_solver.
      destruct (decide (n' ∈ domm I1' ∪ domm I2')); first by set_solver.
      unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
      simpl. apply nzmap_eq. intros kt'.
      rewrite !nzmap_lookup_merge. unfold nat_op.
      rewrite (outflow_map_set_out_map_ne f I1 n S I1' n').
      rewrite (inflow_map_set_out_eq f I2 n S I2').
      auto. auto. auto. auto.
Qed.

Lemma inflow_map_set_valid f I1 I1' n S :
      n ∈ domm I1 →
        I1' = inflow_map_set f I1 n S →
          ✓ I1 → ✓ I1'.
Proof.
    intros n_domm Hi1_eq Valid1.
  unfold valid, flowint_valid.
  replace I1'. unfold inflow_map_set. 
  destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
  unfold valid, flowint_valid in Valid1. 
  simpl in Valid1. 
  simpl. split.
  - apply map_disjoint_dom.
    simpl.
    destruct Valid1 as [H' _].
    apply map_disjoint_dom in H'. rewrite <-Hi1 in Hi1_eq.
    pose proof (flowint_inflow_map_set_dom _ I1 n S I1' Hi1_eq) as Hdomm.
    rewrite <-Hi1 in n_domm.
    assert (domm I1' = domm I1) as H'' by set_solver.
    unfold domm, dom, flowint_dom in H''.
    replace I1' in H''. unfold inflow_map_set in H''.
    simpl in H''. rewrite Hi1 in H''. simpl in H''.
    rewrite <-Hi1 in H''. apply leibniz_equiv_iff in H''.
    rewrite (dom_insert i) in H'' *; intros H''.
    unfold domm, dom, flowint_dom in n_domm.
    replace I1 in n_domm. simpl in n_domm.
    rewrite dom_insert. set_solver.
  - intros Hi. destruct Valid1 as [_ H'].
    apply nzmap_eq. intros n'.
    rewrite <-Hi1 in Hi. 
    assert (<[n:=nzmap_map_set f S (inf I1 n)]> i !! n = None) as H''.
    { rewrite Hi. by rewrite lookup_empty. }
    rewrite lookup_insert in H''.
    inversion H''.
Qed.    


Lemma outflow_map_set_valid f I1 I1' n S :
      n ∉ domm I1 → 
        domm I1 ≠ ∅ →
          I1' = outflow_map_set f I1 n S →
            ✓ I1 → ✓ I1'.
Proof.
  intros n_domm domm_I1 Hi1_eq Valid1.
  apply intValid_unfold.
  split.
  - replace I1'. unfold outflow_map_set, outflow_map_set.
    discriminate.
  - rewrite intValid_unfold in Valid1 *; intros Valid1.
    apply flowint_outflow_map_set_dom in Hi1_eq as Hi1_domm.
    split.
    + apply map_disjoint_dom.
      apply outflow_map_set_inf in Hi1_eq.
      rewrite Hi1_eq.
      unfold domm, dom, flowint_dom in Hi1_domm.
      rewrite elem_of_subseteq in Hi1_domm *. intros.
      rewrite elem_of_disjoint.
      intros n' HinfI1 HoutI1'.
      destruct (decide (n = n')).
      * unfold domm, dom, flowint_dom in n_domm.
        replace n' in HinfI1. contradiction.
      * pose proof (H0 n' HoutI1').
        apply elem_of_union in H1.
        destruct H1.
        destruct Valid1 as [_ [Valid1 _]].
        apply map_disjoint_dom in Valid1.
        rewrite elem_of_disjoint in Valid1 *; intros Valid1.
        pose proof (Valid1 n' HinfI1 H1).
        contradiction.
        set_solver.
    + intros inf_I1'_emp.
      assert (domm I1' = ∅) as domm_I1'.
      { unfold domm, dom, flowint_dom.
        rewrite inf_I1'_emp.
        set_solver. }      
      unfold domm, dom, flowint_dom in domm_I1'.
      rewrite (outflow_map_set_inf f I1 n S) in domm_I1'.
      unfold domm, dom, flowint_dom in domm_I1.
      contradiction.
      trivial.
Qed.

Lemma flowint_map_set_intComposable f I1 I1' I2 I2' n S :
       (∀ x y, x ≤ y → f x ≤ f y) →
       (∀ k, k ∈ S → (inf I2 n ! k) - (out I1 n ! k) = f (inf I2 n ! k) - f (out I1 n ! k)) →
       n ∈ domm I2 → domm I1 ≠ ∅ →
          I1' = outflow_map_set f I1 n S →
            I2' = inflow_map_set f I2 n S →
            intComposable I1 I2 → 
            intComposable I1' I2'.
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Intcomp.
  assert (n ∉ domm I1) as n_notin_I1.
  { unfold intComposable in Intcomp.
    destruct Intcomp as [_ [_ [H' _]]].
    clear -H' n_in_I2. set_solver. }
  unfold intComposable. repeat split.
  - apply (outflow_map_set_valid f I1 I1' n S); try done.
    by destruct Intcomp as [H' _].
  - apply (inflow_map_set_valid f I2 I2' n S); try done.
    by destruct Intcomp as [_ [H' _]].
  - pose proof (flowint_inflow_map_set_dom f I2 n S I2' Hi2) as domm_2.
    assert (domm I1' = domm I1) as domm_1. 
    { unfold domm, dom, flowint_dom. replace I1'.
      unfold outflow_map_set. unfold inf_map. by simpl. }
    pose proof Intcomp as Intcomp0.
    destruct Intcomp0 as [_ [_ [H' _]]].
    set_solver.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    assert (inf_map I1' = inf_map I1) as Hinf_1.
    { replace I1'. unfold outflow_map_set.
      unfold inf_map. by simpl. }
    rewrite Hinf_1 in Hin'.
    destruct Intcomp as [_ [_ [_ [H' _]]]].
    unfold map_Forall in H'. pose proof H' n' m Hin' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. rewrite nzmap_eq in H' *; intros H'.
    pose proof H' kt' as H'. rewrite !nzmap_lookup_merge in H'.
    unfold nat_op, nat_opinv in H'.
    assert (out I2' n' = out I2 n') as Hout.
    { replace I2'. unfold inflow_map_set.
      unfold out, out_map. by simpl. }
    rewrite Hout. unfold inf. unfold inf in H'.
    by rewrite Hinf_1.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros k.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    pose proof Intcomp as Intcomp0.
    destruct Intcomp0 as [_ [_ [_ [_ H']]]].
    unfold map_Forall in H'. pose proof H' n' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. destruct (decide (n' = n)). 
    + replace n'. replace I1'. unfold outflow_map_set.
      unfold out at 1, out_map at 1. simpl.
      unfold out at 2, out_map at 2. simpl.
      rewrite !nzmap_lookup_total_insert.
      destruct (decide (k ∈ S)).
      * rewrite !nzmap_lookup_total_map_set.
        replace I2' in Hin'. unfold inflow_insert_set in Hin'.
        unfold inf_map at 1 in Hin'. simpl in Hin'.
        rewrite e in Hin'. rewrite lookup_insert in Hin'.
        inversion Hin'. (*rewrite nzmap_lookup_total_insert_set.*)
        replace I2'. unfold inflow_insert_set.
        unfold inf at 2. unfold inf_map at 1. simpl.
        rewrite lookup_insert. simpl.
        rewrite nzmap_lookup_total_map_set.
        pose proof composable_outflow_leq_inflow I1 I2 k n n_in_I2 Intcomp as Hleq. 
        pose proof Hfm (out I1 n ! k) (inf I2 n ! k) Hleq.
        pose proof Hf k e0. lia.
        done. done.
      * unfold inf. rewrite e in Hin'. rewrite Hin'. simpl.
        replace I2' in Hin'. unfold inflow_map_set in Hin'. 
        unfold inf_map at 1 in Hin'. simpl in Hin'. 
        rewrite lookup_insert in Hin'. inversion Hin'.
        rename H1 into Hin2.
        rewrite !nzmap_lookup_total_map_set_ne; try done.
        rewrite e in H'.
        assert (inf_map I2 !! n = Some (inf I2 n)) as H''.
        { unfold inf. destruct (inf_map I2 !! n) eqn: Hi2n.
          by simpl. unfold domm, dom, flowint_dom in n_in_I2.
          rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
          rewrite Hi2n in n_in_I2. 
          destruct n_in_I2 as [x Hx]; inversion Hx. } 
        pose proof H' (inf I2 n) H'' as Heq.
        rewrite nzmap_eq in Heq *; intros Heq.
        pose proof Heq k as Heq. 
        rewrite !nzmap_lookup_merge in Heq.
        by unfold nat_op, nat_opinv in Heq.
    + assert (inf I2' n' = inf I2 n') as Hin. 
      { replace I2'. unfold inflow_insert_set.
      unfold inf at 1, inf_map at 1. simpl.
      rewrite lookup_insert_ne; try done. }
      rewrite Hin. replace I2' in Hin'.
      unfold inflow_insert_set, inflow_map_set in Hin'.
      unfold inf at 1, inf_map at 1 in Hin'. simpl in Hin'.
      rewrite lookup_insert_ne in Hin'; try done. 
      pose proof H' m Hin' as H'.
      rewrite nzmap_eq in H' *; intros H'.
      pose proof H' k as H'.
      rewrite !nzmap_lookup_merge in H'.
      unfold nat_op, nat_opinv in H'.
      assert (out I1' n' = out I1 n') as Hout.
      { replace I1'. unfold outflow_map_set.
        unfold out at 1, out_map at 1. simpl.
        rewrite nzmap_lookup_total_insert_ne; try done. }
      by rewrite Hout.  
Qed.


Lemma flowint_map_set_valid f I1 I1' I2 I2' n S :
  (∀ x y, x ≤ y → f x ≤ f y) →
  (∀ k, k ∈ S → (inf I2 n ! k) - (out I1 n ! k) = f (inf I2 n ! k) - f (out I1 n ! k)) →
      n ∈ domm I2 → domm I1 ≠ ∅ →
        I1' = outflow_map_set f I1 n S →
          I2' = inflow_map_set f I2 n S →
            ✓ (I1 ⋅ I2) → ✓ (I1' ⋅ I2').
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof intComposable_valid I1 I2 Valid_12 as Intcomp_12.
  apply intValid_composable. 
  apply (flowint_map_set_intComposable f I1 I1' I2 I2' n S); try done.
Qed.


Lemma flowint_map_set_eq f (I1 I1' I2 I2': multiset_flowint_ur) n S :
  (∀ x y, x ≤ y → f x ≤ f y) →
  (∀ k, k ∈ S → (inf I2 n ! k) - (out I1 n ! k) = f (inf I2 n ! k) - f (out I1 n ! k)) →
  n ∈ domm I2 → domm I1 ≠ ∅ →
  I1' = outflow_map_set f I1 n S →
  I2' = inflow_map_set f I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof (intComposable_valid _ _ Valid_12) as HintComp.
  pose proof (flowint_map_set_valid f I1 I1' I2 I2' n S 
                Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12) as Valid_12'.
  pose proof (intComposable_valid _ _ Valid_12') as HintComp'.   
  destruct (I1⋅I2) as [ [i o] | ] eqn: Hi12; [| exfalso; try done].
  unfold op, intComp in Hi12.
  destruct (decide (intComposable I1 I2)); last done.
  inversion Hi12.
  destruct (I1'⋅I2') as [ [i' o'] | ] eqn: Hi12'; [| exfalso; try done].    
  unfold op, intComp in Hi12'.
  destruct (decide (intComposable I1' I2')); last done.
  inversion Hi12'.
  apply intValid_composable in HintComp.
  assert (infComp I1 I2 = infComp I1' I2') as Hinfcomp.
  { apply (flowint_map_set_infComp f I1 I1' I2 I2' n S); try done. }
  pose proof (flowint_map_set_outComp _ I1 I1' I2 I2' n S n_in_I2 Hi1 Hi2) as Houtcomp.
    by rewrite Hinfcomp Houtcomp.
Qed.

Lemma flowint_insert_eq (I1 I1' I2 I2': multiset_flowint_ur) n S :
  n ∈ domm I2 → domm I1 ≠ ∅ →
  I1' = outflow_insert_set I1 n S →
  I2' = inflow_insert_set I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  apply flowint_map_set_eq.
  all: lia.
Qed.

Lemma flowint_delete_eq (I1 I1' I2 I2': multiset_flowint_ur) n S :
  (∀ k, k ∈ S → 1 ≤ out I1 n ! k) →
  n ∈ domm I2 → domm I1 ≠ ∅ →
  I1' = outflow_delete_set I1 n S →
  I2' = inflow_delete_set I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros.
  apply (flowint_map_set_eq (λ n, n - 1) I1 I1' I2 I2' n S).
  lia.
  intros.
  pose proof H0 k H6.
  lia.
  all: auto.
Qed.

Lemma inflow_insert_set_inset I n S I' :
      I' = inflow_insert_set I n S → 
           inset I' n = inset I n ∪ S.
Proof.
  intros Heq. unfold inset.
  unfold multiset_flows.dom_ms.
  replace I'. unfold inflow_insert_set.
  unfold inflow_map_set. unfold inf at 1; simpl.
  rewrite lookup_insert. simpl.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_map_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_map_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.

Lemma inflow_delete_set_inset I n S I' :
      (∀ k, k ∈ S → inf I n ! k ≤ 1) →
        I' = inflow_delete_set I n S → 
           inset I' n = inset I n ∖ S.
Proof.
  intros Hkb Heq. unfold inset.
  unfold multiset_flows.dom_ms.
  replace I'. unfold inflow_delete_set.
  unfold inf at 1. simpl.
  rewrite lookup_insert. simpl.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - intros. apply Hkb in e as HxB.
    rewrite nzmap_lookup_total_map_set in H0.
    unfold ccmunit, ccm_unit, nat_ccm, nat_unit in H0. simpl.
    assert (inf I n ! x - 1 = 0). lia.
    contradiction. done.
  - intros. set_solver.
  - intros. rewrite nzmap_lookup_total_map_set_ne in H0.
    rewrite elem_of_difference.
    split.
    rewrite nzmap_elem_of_dom_total.
    all: done.
  - intros. rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_difference in H0 *; intros.
    destruct H0 as [H0 _].
    rewrite nzmap_elem_of_dom_total in H0 *; intros.
    unfold out. all: done.
Qed.

Lemma inflow_delete_set_inset_ne I n S I' n' :
      n' ≠ n → I' = inflow_delete_set I n S → 
           inset I' n' = inset I n'.
Proof.
  unfold inset.
  pose proof (inflow_map_set_ne (λ n, n - 1) I n S I' n').
  intros.
  unfold inf.
  rewrite H0; done.
Qed.


Lemma flowint_inflow_delete_set_dom (I: multiset_flowint_ur) n S I':
    I' = inflow_delete_set I n S
    → domm I' = domm I ∪ {[n]}.
Proof.
  intros Heq.
  unfold domm, dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne (λ n, n - 1) I n S I' n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      rewrite Heq.
      unfold inflow_insert_set.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.      

Lemma flowint_inflow_insert_set_dom (I: multiset_flowint_ur) n S I':
    I' = inflow_insert_set I n S
    → domm I' = domm I ∪ {[n]}.
Proof.
  intros Heq.
  unfold domm, dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne (λ n, n + 1) I n S I' n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      rewrite Heq.
      unfold inflow_insert_set.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.

End multiset_flows.

Arguments multiset_flowint_ur _ {_ _} : assert.
Arguments inset _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ _ _ : assert.
Arguments in_outsets _ {_ _} _ _ : assert.
Arguments closed _ {_ _} _ : assert.

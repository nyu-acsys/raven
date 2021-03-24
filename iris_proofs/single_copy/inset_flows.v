Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm multiset_flows keyset_ra.

(** Flow interface cameras and auxiliary lemmas for inset flows
  (used in the give-up template proof). *)

Section inset_flows.

Context `{Countable K}.

Definition KS := @KS K _ _.

(** Keysets of flow interfaces *)

Definition keyset (I : multiset_flowint_ur K) n := dom_ms (inf I n) ∖ dom_ms (out I n).

Lemma keyset_def : ∀ k I_n n, k ∈ inset K I_n n → ¬ in_outsets K k I_n
  → k ∈ keyset I_n n.
Proof.
  intros ? ? ? k_in_inset k_not_in_outsets.
  unfold keyset.
  unfold inset in k_in_inset.
  unfold in_outsets in k_not_in_outsets.
  rewrite elem_of_difference.
  naive_solver.
Qed.

(* The global invariant ϕ. *)
Definition globalinv root I :=
  ✓I
  ∧ (root ∈ domm I)
  ∧ closed K I
  ∧ (∀ k, k ∈ KS → k ∈ inset K I root).

(** Assorted lemmas about inset flows used in the template proofs *)

Lemma globalinv_root_fp: ∀ I root, globalinv root I → root ∈ domm I.
Proof.
  intros I root Hglob. unfold globalinv in Hglob.
  destruct Hglob as [H1 [H2 H3]]. done.
Qed.

Lemma contextualLeq_impl_globalinv : ∀ I I' root,
    globalinv root I →
    contextualLeq K_multiset I I' →
    (∀ n, n ∈ domm I' ∖ domm I → inset K I' n = ∅) →
    globalinv root I'.
Proof.
  intros ? ? ? GI CLeq InfI'.
  unfold contextualLeq in CLeq.
  unfold globalinv in GI.
  destruct GI as (_ & DomR & OutI & InfI).
  destruct CLeq as (VI & VI' & DS & InfR & OutR).
  unfold closed in OutI.
  unfold globalinv, closed.
  repeat split.
  - trivial.
  - set_solver.
  - intros.
    destruct (decide (n ∈ domm I')).
    * apply flowint_valid_unfold in VI'.
      destruct VI' as [Ir' (I'_def & I'_disj & _)].
      rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in I'_disj *.
      intros.
      assert (out_map I' ! n = 0%CCM).
      { unfold out_map. rewrite I'_def.
        assert (¬ (n ∈ dom (gset Node) (out_map I'))).
        { unfold domm, dom, flowint_dom in e.
          set_solver.
        }
        rewrite I'_def in H1.
        rewrite nzmap_elem_of_dom_total in H1 *.
        intros.
        apply dec_stable in H1.
        unfold out_map in H1.
        by rewrite H1.
      }
      unfold outset, multiset_flows.dom_ms, nzmap_dom, out.
      rewrite H1. simpl.
      rewrite dom_empty.
      apply not_elem_of_empty.
    * assert (n ∉ domm I) by set_solver.
      pose proof (OutR n n0). 
      unfold outset, multiset_flows.K_multiset, multiset_flows.K_multiset_ccm.
      unfold K_multiset, K_multiset_ccm in H1. rewrite <- H1.
      pose proof (OutI k n).
      unfold outset in H2.
      trivial.
  - intros.
    (*destruct H2 as (H2 & _).*)
    specialize (InfI k).
    (*rewrite <- H0 in DomR.*)
    specialize (InfR root DomR).
    unfold inset.
    unfold inset in InfR.
    rewrite <- InfR.
    apply InfI in H0.
    trivial.
Qed.

Lemma globalinv_root_ins : ∀ I Ir root k,
    globalinv root I ∧ Ir ≼ I ∧ domm Ir = {[root]} ∧ k ∈ KS
    → k ∈ inset K Ir root.
Proof.
  intros I Ir root k ((Hv & _ & _ & Hl) & [I2 Hincl] & Hdom & kKS).
  specialize (Hl k kKS). 
  apply (inset_monotone I Ir I2 k root); try done.
  set_solver.
Qed.


End inset_flows.


Arguments keyset _ {_ _} _ _ : assert.
Arguments globalinv _ {_ _} _ _ : assert.

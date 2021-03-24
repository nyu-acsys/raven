(** Abstract specification of search structure operations *)

From iris.algebra Require Import gset.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export iprop.
From iris.base_logic.lib Require Export invariants.

Set Default Proof Using "All".


Section Search_Structure.

(* The set of keys. *)
Context `{Countable K}.

(* The search structure operations *)
Inductive dOp := searchOp | insertOp | deleteOp.

(* Specification of a search structure operation *)
Definition Ψ dop k (C: gsetO K) (C': gsetO K) (res: bool) :=
  match dop with
  | searchOp => C' = C ∧ (if res then k ∈ C else k ∉ C)
  | insertOp => C' = C ∪ {[k]} ∧ (if res then k ∉ C else k ∈ C)
  | deleteOp => C' = C ∖ {[k]} ∧ (if res then k ∈ C else k ∉ C)
  end.

Lemma Ψ_impl_C_in_K dop k C C' res (Ks: gset K) :
  Ψ dop k C C' res → C ⊆ Ks → k ∈ Ks → C' ⊆ Ks.
Proof.
  intros HΨ ? ?. unfold Ψ in HΨ.
  destruct dop.
  - destruct HΨ as [HΨ _]. subst C'. done.
  - destruct HΨ as [HΨ _]. set_solver.
  - destruct HΨ as [HΨ _]. set_solver.
Qed.

End Search_Structure.

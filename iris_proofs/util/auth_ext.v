(** Assorted auxiliary lemmas for authoritative RAs *)

From iris.algebra Require Import excl auth gmap agree gset.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".

Lemma auth_own_incl `{inG Σ (authR A)} `{!CmraDiscrete A} γ (x y: A) :
  own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
Proof.
  rewrite -own_op. rewrite own_valid. iPureIntro.
  rewrite auth_both_valid_discrete.
  simpl. intros H1. destruct H1 as [z H2]. (*destruct H2 as [a Ha]. destruct Ha as [Ha Hb].*)
  apply z.
Qed.

Lemma auth_excl_update `{inG Σ (authR (optionUR (exclR A)))} `{OfeDiscrete A} γ ys xs1 xs2 :
  own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
          with "Hγ● Hγ◯") as "[$$]".
  { apply auth_update. apply option_local_update. apply exclusive_local_update. done. }
  done.
Qed.

(*
Lemma auth_agree  `{inG Σ (authR (optionUR (exclR A)))} `{OfeDiscrete A} γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
Proof.
  iIntros "Hγ● Hγ◯". iPoseProof (own_valid_2 with "Hγ● Hγ◯") as "H".
  iEval (rewrite auth_both_valid) in "H".
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
Qed.
*)
From diaframe.heap_lang Require Import proof_automation wp_auto_lob.
From diaframe.lib Require Import own_hints.
From iris.algebra Require Import agree frac excl.

Definition new_lock : val :=
  λ: "_", ref (ref #false).

Definition new_node : val :=
  λ: "_",
    let: "ret" := AllocN #2 NONE in
    "ret" <- ref #false;;
    "ret".

Definition wait_on : val :=
  rec: "wait_on" "l" :=
    if: ! "l" then
      "wait_on" "l"
    else
      #().

Definition acquire : val :=
  λ: "lk" "node",
    let: "l" := ! "node" in
    "l" <- #true;;
    let: "pred" := Xchg "lk" "l" in  (* also called fetch_and_store sometimes *)
    ("node" +ₗ #1) <- "pred";;
    wait_on "pred".

Definition release : val :=
  λ: "node",
    ! "node" <- #false;;
    "node" <- ! ("node" +ₗ #1).

Definition clh_lockR := prodR (agreeR $ leibnizO loc) fracR.
Class clh_lockG Σ := CLHLockG {
  #[local] clh_lock_tokG :: inG Σ clh_lockR;
  #[local] clh_lock_exclG :: inG Σ $ exclR unitO
}.
Definition clh_lockΣ : gFunctors := #[GFunctor clh_lockR; GFunctor $ exclR unitO].

#[local] Obligation Tactic := program_verify.

Global Program Instance subG_clh_lockΣ {Σ} : subG clh_lockΣ Σ → clh_lockG Σ.

Section spec.
  Context `{!heapGS Σ, clh_lockG Σ}.

  Let N := nroot .@ "clhlock".
  Definition N_node := N .@ "node".

  Definition queued_loc γe l γ R : iProp Σ :=
    own γ (to_agree l, 1%Qp) ∨ (∃ (b : bool), l ↦{#1/2} #b ∗ (⌜b = true⌝ ∨ (⌜b = false⌝ ∗ R ∗ own γe (Excl ()) ∗ own γ (to_agree l, 1/2)%Qp ∗ l ↦{#1/2} #b))).
  (* a unique pair that owns the node *)

  Definition free_node n : iProp Σ :=
    ∃ (l : loc) v, n ↦ #l ∗ (n +ₗ 1) ↦ v ∗ l ↦ #false.

  Definition acquired_node γe n R : iProp Σ :=
    ∃ (l p : loc), n ↦ #l ∗ (∃ γ, inv N_node (queued_loc γe l γ R) ∗ own γ (to_agree l, 1/2)%Qp) ∗ l ↦{#1/2} #true ∗
                  (n +ₗ 1) ↦ #p ∗ p ↦ #false ∗ own γe (Excl ()).

  Definition lock_inv γe lk R : iProp Σ :=
    ∃ (l : loc), lk ↦ #l ∗ ∃ γ, own γ (to_agree l, 1/2)%Qp ∗ inv N_node (queued_loc γe l γ R).

  Definition is_lock γe R v : iProp Σ :=
    ∃ (lk : loc), ⌜v = #lk⌝ ∗ inv N (lock_inv γe lk R).

  Global Program Instance new_lock_spec :
    SPEC {{ True }}
      new_lock #()
    {{ (lk : val), RET lk; (∀ R, R ={⊤}=∗ ∃ γe, is_lock γe R lk) }}.

  Global Program Instance new_node_spec :
    SPEC {{ True }}
      new_node #()
    {{ (n : loc), RET #n; free_node n }}.

  Global Program Instance acquire_spec R (n : loc) (lk : val) γe :
    SPEC {{ is_lock γe R lk ∗ free_node n }}
      acquire lk #n
    {{ RET #(); R ∗ acquired_node γe n R }}.

  Global Program Instance release_spec R (n : loc) γe :
    SPEC {{ R ∗ acquired_node γe n R }}
      release #n
    {{ RET #(); free_node n }}.

  Definition acquired_mutual_exclusion γe n m R : acquired_node γe n R ∗ acquired_node γe m R ⊢ False
    := verify. (* Cannot do Lemma _ : _ := verify unfortunately. If proper reuse is wanted this should be a Mergable instance *)
End spec.

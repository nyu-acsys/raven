(** Code borrowed from Iris/examples repository : https://gitlab.mpi-sws.org/iris/examples/ *)
(** File at /theories/proph/lib/one_shot_proph.v *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition val_of_list (vs : list (val * val)) : val :=
  match vs with
  | []          => #()
  | (_, v) :: _ => v
  end.

(** Specification for one-shot prophecy variables. *)

Section one_shot.
  Context `{!heapG Σ}.

  Definition proph1 (p : proph_id) (v : val) :=
    (∃ vs, proph p vs ∗ ⌜match vs with [] => True | (_,w) :: _ => v = w end⌝)%I.

  Lemma proph1_exclusive (p : proph_id) (v1 v2 : val) :
    proph1 p v1 -∗ proph1 p v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (vs1) "[Hp1 _]".
    iDestruct "H2" as (vs2) "[Hp2 _]".
    iApply (proph_exclusive with "Hp1 Hp2").
  Qed.

  Lemma wp_new_proph1 s E :
    {{{ True }}}
      NewProph @ s; E
    {{{ p v, RET (LitV (LitProphecy p)); proph1 p v }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp". iApply ("HΦ" $! p (val_of_list vs)).
    iExists _. iFrame "Hp". iPureIntro. by case vs as [|[v w] vs].
  Qed.

  Lemma wp_resolve1 s E e Φ (p : proph_id) (v w : val) :
    Atomic StronglyAtomic e →
    to_val e = None →
    proph1 p v -∗
    WP e @ s; E {{ r, ⌜v = w⌝ -∗ Φ r }} -∗
    WP Resolve e (Val $ LitV $ LitProphecy p) (Val w) @ s; E {{ Φ }}.
  Proof.
    iIntros (A He) "Hp Wpe". iDestruct "Hp" as (vs) "[Hp HEq]".
    iDestruct "HEq" as %HEq. wp_apply (wp_resolve with "Hp"); try done.
    iApply wp_mono; last done. iIntros (v0) "H". iIntros (pvs ->) "Hp".
    by iApply "H".
  Qed.
End one_shot.

(** Alternative specification. *)

Section one_shot'.
  Context `{!heapG Σ}.

  Definition proph1' (p : proph_id) (v : val) :=
    (∃ vs, proph p vs ∗ ⌜val_of_list vs = v⌝)%I.

  Lemma proph1'_exclusive (p : proph_id) (v1 v2 : val) :
    proph1' p v1 -∗ proph1' p v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (vs1) "[Hp1 _]".
    iDestruct "H2" as (vs2) "[Hp2 _]".
    iApply (proph_exclusive with "Hp1 Hp2").
  Qed.

  Lemma wp_new_proph1' s E :
    {{{ True }}}
      NewProph @ s; E
    {{{ p v, RET (LitV (LitProphecy p)); proph1' p v }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_apply wp_new_proph; first done.
    iIntros (pvs p) "Hp". iApply "HΦ". iExists _. by iFrame.
  Qed.

  Lemma wp_resolve1' s E e Φ (p : proph_id) (v w : val) :
    Atomic StronglyAtomic e →
    to_val e = None →
    proph1' p v -∗
    WP e @ s; E {{ r, ⌜v = w⌝ -∗ Φ r }} -∗
    WP Resolve e (Val $ LitV $ LitProphecy p) (Val w) @ s; E {{ Φ }}.
  Proof.
    iIntros (A He) "Hp Wpe". iDestruct "Hp" as (vs) "[Hp <-]".
    wp_apply (wp_resolve with "Hp"); try done. iApply wp_mono; last done.
    iIntros (v) "H". iIntros (pvs ->) "Hp". by iApply "H".
  Qed.
End one_shot'.

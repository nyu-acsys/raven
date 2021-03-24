(** Code borrowed from Iris/examples repository : https://gitlab.mpi-sws.org/iris/examples/ *)
(** File at /theories/proph/lib/typed_proph.v *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** A library defining a typed wrapper for prophecy variables. *)

Record TypedProphSpec := mkTypedProphSpec
 { typed_proph_spec_type     : Type
 ; typed_proph_spec_from_val : val → option typed_proph_spec_type
 ; typed_proph_spec_to_val   : typed_proph_spec_type → val
 ; typed_proph_spec_inj_prop :
     ∀ x, typed_proph_spec_from_val (typed_proph_spec_to_val x) = Some x }.

Fixpoint process_prophecy {A} (f : val → option A) (vs : list (val * val)) : list A :=
  match vs with
  | []        => []
  | (_,w)::vs =>
    match f w with
    | None   => []
    | Some w => w :: process_prophecy f vs
    end
   end.

Definition process_prophecy1 {A} {hA : Inhabited A} (f : val → option A) (vs : list (val * val)) : A :=
  match vs with
  | []        => inhabitant
  | (v,w)::vs => default inhabitant (f w)
  end.

Section TypedProph.
Context `{!heapG Σ}.

Notation iProp := (iProp Σ).

Record TypedProph := mkTypedProph
  { typed_proph_type             : Type
  ; typed_proph_from_val         : val → option typed_proph_type
  ; typed_proph_to_val           : typed_proph_type → val
  ; typed_proph_inj_prop         :
      ∀ x, typed_proph_from_val (typed_proph_to_val x) = Some x
  ; typed_proph_prop             : proph_id → list typed_proph_type → iProp
  ; typed_proph_prop_excl        : ∀ p l1 l2, typed_proph_prop p l1 ∗ typed_proph_prop p l2 -∗ False
  ; typed_proph_wp_new_proph s E :
      {{{ True }}}
        NewProph @ s; E
      {{{ pvs p, RET (LitV (LitProphecy p)); typed_proph_prop p pvs }}}
  ; typed_proph_wp_resolve s E e Φ p v w pvs :
      Atomic StronglyAtomic e →
      to_val e = None →
      w = typed_proph_to_val v →
      typed_proph_prop p pvs -∗
      WP e @ s; E {{ r, ∀ pvs', ⌜pvs = v :: pvs'⌝ -∗ typed_proph_prop p pvs' -∗ Φ r }} -∗
      WP Resolve e (Val $ LitV $ LitProphecy p) (Val w) @ s; E {{ Φ }}
  ; typed_proph1_prop `{Inhabited typed_proph_type}
                                 : proph_id → typed_proph_type → iProp
  ; typed_proph1_prop_excl `{!Inhabited typed_proph_type}
                                 : ∀ p o1 o2, typed_proph1_prop p o1 ∗ typed_proph1_prop p o2 -∗ False
  ; typed_proph_wp_new_proph1 `{!Inhabited typed_proph_type} s E :
      {{{ True }}}
        NewProph @ s; E
      {{{ v p, RET #p; typed_proph1_prop p v }}}
  ; typed_proph_wp_resolve1 `{!Inhabited typed_proph_type} s E e Φ p w v1 v2 :
      Atomic StronglyAtomic e →
      to_val e = None →
      typed_proph_from_val w = Some v2 →
      typed_proph1_prop p v1 -∗
      WP e @ s; E {{ r, ⌜v1 = v2⌝ -∗ Φ r }} -∗
      WP Resolve e (Val $ LitV $ LitProphecy p) (Val w) @ s; E {{ Φ }} }.

Program Definition make_TypedProph (spec : TypedProphSpec) : TypedProph :=
  {| typed_proph_type := typed_proph_spec_type spec
   ; typed_proph_from_val := typed_proph_spec_from_val spec
   ; typed_proph_to_val := typed_proph_spec_to_val spec
   ; typed_proph_prop p l :=
       (∃ vs, ⌜l = process_prophecy (typed_proph_spec_from_val spec) vs⌝ ∗ proph p vs)%I
   ; typed_proph1_prop _ p v :=
       (∃ vs, ⌜v = process_prophecy1 (typed_proph_spec_from_val spec) vs⌝ ∗ proph p vs)%I |}.
Next Obligation.
  intros spec. exact (typed_proph_spec_inj_prop spec).
Qed.
Next Obligation.
  intros spec.
  iIntros (p l1 l2) "[H1 H2]".
  iDestruct "H1" as (vs1) "[_ H1]".
  iDestruct "H2" as (vs2) "[_ H2]".
  iApply (proph_exclusive with "H1 H2").
Qed.
Next Obligation.
  intros spec.
  iIntros (s E Φ) "_ HΦ". wp_apply wp_new_proph; first done.
  iIntros (pvs p) "Hp". iApply "HΦ". iExists pvs. by iFrame.
Qed.
Next Obligation.
  intros spec.
  iIntros (s E e Φ p v w pvs H1 H2 H3) "H HΦ". iDestruct "H" as (vs) "[-> Hp]".
  wp_apply (wp_resolve with "Hp"); first done. iApply (wp_wand with "HΦ").
  iIntros (vΦ) "H". iIntros (pvs' ->) "Hp". iApply "H".
  + iPureIntro. by rewrite H3 /= (typed_proph_spec_inj_prop spec).
  + iExists pvs'. by iFrame.
Qed.
Next Obligation.
  intros spec ?.
  iIntros (p o1 o2) "[H1 H2]".
  iDestruct "H1" as (vs1) "[_ H1]".
  iDestruct "H2" as (vs2) "[_ H2]".
  iApply (proph_exclusive with "H1 H2").
Qed.
Next Obligation.
  intros spec ?.
  iIntros (s E Φ) "_ HΦ". wp_apply wp_new_proph; first done.
  iIntros (pvs p) "Hp". iApply "HΦ". iExists pvs. by iFrame.
Qed.
Next Obligation.
  intros spec ?.
  iIntros (s E e Φ p w v1 v2 H1 H2 H3) "H HΦ". iDestruct "H" as (vs) "[-> Hp]".
  wp_apply (wp_resolve with "Hp"); first done. iApply (wp_wand with "HΦ").
  iIntros (v) "H". iIntros (pvs' ->) "Hp". iApply "H".
  iPureIntro. simpl. by rewrite H3.
Qed.
End TypedProph.

(** Instantiation of the interface with booleans. *)

Section bool_proph.
  Definition bool_from_val (v : val) : option bool :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.

  Definition bool_to_val (b : bool) : val := LitV(LitBool b).

  Lemma bool_inj_prop : ∀ (b : bool), bool_from_val (bool_to_val b) = Some b.
  Proof. done. Qed.

  Definition BoolProph : TypedProphSpec :=
    mkTypedProphSpec bool bool_from_val bool_to_val bool_inj_prop.
End bool_proph.

Definition BoolTypedProph `{!heapG Σ} := make_TypedProph BoolProph.

(** Instantiation of the interface with integers. *)

Section int_proph.
  Definition int_from_val (v : val) : option Z :=
    match v with
    | LitV(LitInt i) => Some i
    | _              => None
    end.

  Definition int_to_val (i : Z) : val := LitV(LitInt i).

  Lemma int_inj_prop : ∀ (i : Z), int_from_val (int_to_val i) = Some i.
  Proof. done. Qed.

  Definition IntProph : TypedProphSpec :=
    mkTypedProphSpec Z int_from_val int_to_val int_inj_prop.
End int_proph.

Definition IntTypedProph `{!heapG Σ} := make_TypedProph IntProph.

(** Instantiation of the interface with nats. *)

Section nat_proph.
  Definition nat_from_val (v : val) : option nat :=
    match v with
    | LitV(LitInt i) => Some (Z.to_nat i)
    | _              => None
    end.

  Definition nat_to_val (i : nat) : val := LitV(LitInt i).

  Lemma nat_inj_prop : ∀ (i : nat), nat_from_val (nat_to_val i) = Some i.
  Proof. 
    intros i. simpl. apply f_equal. lia.
  Qed.

  Definition NatProph : TypedProphSpec :=
    mkTypedProphSpec nat nat_from_val nat_to_val nat_inj_prop.
End nat_proph.

Definition NatTypedProph `{!heapG Σ} := make_TypedProph NatProph.

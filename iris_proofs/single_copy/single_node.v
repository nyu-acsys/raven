(** Verification of a simple example template: a single-node structure *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import auth_ext search_str.

(** We use integers as keys. *)
Definition K := Z.

(* The keyspace is some arbitrary finite subset of K. *)
Parameter KS : gset K.


(** Definitions of cameras used in the template verification *)
Section One_Node_Cameras.

  (* RA for fractional set of keys *)
  Definition frackeysCmra : cmra := frac_agreeR (gsetUR K).

  Class frackeysG Σ :=
    FrackeyshG { frackeys_inG :> inG Σ  frackeysCmra}.
  Definition frackeysΣ : gFunctors := #[GFunctor frackeysCmra].

  Instance subG_frackeysΣ {Σ} : subG frackeysΣ Σ → frackeysG Σ.
  Proof. solve_inG. Qed.

End One_Node_Cameras.


(** Syntactic sugar for fraction-set RA *)
Notation "γ ⤇[ q ] m" := (own γ (to_frac_agree q m))
  (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
Notation "γ ⤇½ m" := (own γ (to_frac_agree (1/2) m))
  (at level 20, format "γ ⤇½  m") : bi_scope.

(** Verification of the template *)
Section One_Node_Template.

  Context `{!heapG Σ, !frackeysG Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. *)

  Parameter allocRoot : val.
  Parameter decisiveOp : (dOp → val).

  Definition create : val :=
    λ: <>,
      let: "r" := allocRoot #() in
      "r".  

  Definition CSSOp (Ψ: dOp) (r: Node) : val :=
    rec: "dictOp" "k" :=
      lockNode #r;;
      let: "res" := ((decisiveOp Ψ) #r "k") in
      unlockNode #r;;
      "res".

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. *)
  Parameter node : Node → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n C, Timeless (node n C).
  Instance node_timeless n C: Timeless (node n C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-give-up.spl and b+-tree.spl *)
  Hypothesis node_sep_star: ∀ n C C',
    node n C ∗ node n C' -∗ False.


  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper *)

  Parameter allocRoot_spec :
      ⊢ ({{{ True }}}
           allocRoot #()
         {{{ (r: Node),
             RET #r; node r ∅ ∗ (lockLoc r) ↦ #false  }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n C }}}
           decisiveOp dop #n #k
         {{{ (res: bool) (C1: gset K),
             RET #res;
             node n C1 ∗ ⌜Ψ dop k C C1 res⌝ }}})%I.

  (** The concurrent search structure invariant *)

  Definition nodePred γ n : iProp :=
    ∃ C, node n C
    ∗ γ ⤇½ C.

  Definition CSS γ r (C: gset K) : iProp :=
    ∃ (b: bool),
      γ ⤇½ C
      ∗ lockR b r (nodePred γ r).

  (** High-level lock specs **)

  Lemma lockNode_spec_high γ (r: Node) :
    ⊢  <<< ∀ (C: gset K), CSS γ r C >>>
         lockNode #r @ ⊤
       <<< CSS γ r C ∗ nodePred γ r, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". 
    awp_apply (lockNode_spec r).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss". iDestruct "Hcss" as (b) "(HC & Hlock)".  
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro. iSplitL.
      iFrame. iExists b. iFrame.
      eauto with iFrame.
    }
    iIntros "(Hlockn & Hnp)". iModIntro. 
    iSplitL. iFrame. iExists true. iFrame.
    eauto with iFrame. 
  Qed.
  
  Lemma unlockNode_spec_high γ (r: Node) :
    ⊢  nodePred γ r -∗ 
        <<< ∀ (C: gset K), CSS γ r C >>>
          unlockNode #r @ ⊤
       <<< CSS γ r C, RET #() >>>.
  Proof.
    iIntros "Hnp" (Φ) "AU". 
    awp_apply (unlockNode_spec r).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (b) "(HC & Hlock)".
    iAssert (⌜b = true⌝)%I as "%".
    { destruct b; try done.
      iDestruct "Hlock" as "(_ & Hnp')".
      iDestruct "Hnp" as (Cn)"(node & _)".
      iDestruct "Hnp'" as (Cn')"(node' & _)".
      iExFalso; iApply (node_sep_star r); try iFrame. }
    subst b.      
    iCombine "Hlock Hnp" as "HlockR". 
    iAaccIntro with "HlockR".
    { iIntros "(Hlockn & Hnp)". iModIntro. iSplitR "Hnp".
      iFrame. iExists true. iFrame.
      iIntros "AU". iModIntro. iFrame. }
    iIntros "Hlockn". iModIntro. 
    iSplitL. iFrame. iExists false. iFrame.
    eauto with iFrame. 
  Qed.
  

  (** Proof of CSSOp *)

  Theorem create_spec :
   ⊢ {{{ True }}}
        create #()
     {{{ γ (r: Node), RET #r; CSS γ r ∅ }}}.
  Proof.
    iIntros (Φ). iModIntro.
    iIntros "_ HΦ".
    wp_lam. wp_apply allocRoot_spec; try done.
    iIntros (r) "(node & Hl)". iApply fupd_wp.
    iMod (own_alloc (to_frac_agree (1) (∅: gset K))) 
          as (γ)"Hf". { try done. }
    iEval (rewrite <-Qp_half_half) in "Hf".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hf". 
    iDestruct "Hf" as "(Hf & Hf')".
    iModIntro. wp_pures.
    iModIntro. iApply ("HΦ" $! γ r).
    iExists false. iFrame.
    iExists ∅. iFrame.
  Qed.     

  Theorem CSSOp_spec (γ: gname) r (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ r C >>>
                          CSSOp dop r #k @ ⊤
                 <<< ∃ C' (res: bool), CSS γ r C'
                                     ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". wp_lam. wp_bind(lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ r); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros "(HInv & Hnode)".
    (* Close AU and move on *)
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnode" as (Cn) "(Hn & Hcn)".
    wp_apply ((decisiveOp_spec dop r k) with "[Hn]"). eauto with iFrame.
    iIntros (res C') "(Hn & %)".
    wp_pures.

    awp_apply (unlockNode_spec_low).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (b)"(HC & Hlock)".
    iAssert (⌜C = Cn⌝)%I as "%".
    { iPoseProof (own_valid_2 _ _ _ with "[$Hcn] [$HC]") as "H'".
      iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
      destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
      by iPureIntro. } subst Cn.
    iAssert (⌜b = true⌝)%I with "[-]" as "%".
    {
      destruct b.
      - by iPureIntro.
      - iExFalso. iDestruct "Hlock" as "(_ & Hn')".
        iDestruct "Hn'" as (C1)"(Hn' & _)".
        iApply node_sep_star; iFrame.
    } subst b.
    iEval (unfold lockR) in "Hlock".
    iDestruct "Hlock" as "(Hl & _)".
    iAaccIntro with "Hl".
    { iIntros "Hl". iModIntro.
      iSplitR "Hcn Hn".
      { iExists true. iFrame. }
      iIntros "AU". iModIntro. iFrame. }
    iIntros "Hl". 
    iCombine "Hcn HC" as "H'". 
    iEval (rewrite <-frac_agree_op) in "H'". 
    iEval (rewrite Qp_half_half) in "H'".
    iMod ((own_update (γ) (to_frac_agree 1 C) 
                  (to_frac_agree 1 C')) with "[$H']") as "H'".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid_instance.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "H'".
    iEval (rewrite frac_agree_op) in "H'".  
    iDestruct "H'" as "(Hcn & HC)".
    iModIntro. iExists C', res.
    iSplitL. iFrame "∗%". iExists false. iFrame.
    iExists C'. iFrame.
    iIntros "HΦ". iModIntro. wp_pures.
    by iModIntro.
  Qed.

End One_Node_Template.

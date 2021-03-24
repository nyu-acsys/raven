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
Definition frac_contR := frac_agreeR (gsetUR K).
Definition cont_exclR := authR $ optionUR $ exclR (gsetO K).

Class onenodeG Σ := ONENODE {
                        onenode_frac_contG :> inG Σ frac_contR;
                        onenode_cont_exclG :> inG Σ cont_exclR;
                      }.

Definition onenodeΣ : gFunctors :=
  #[GFunctor frac_contR; GFunctor cont_exclR].

Instance subG_onenodeΣ {Σ} : subG onenodeΣ Σ → onenodeG Σ.
Proof. solve_inG. Qed.

(** Syntactic sugar for fraction-set RA *)
Notation "γ ⤇[ q ] m" := (own γ (to_frac_agree q m))
  (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
Notation "γ ⤇½ m" := (own γ (to_frac_agree (1/2) m))
  (at level 20, format "γ ⤇½  m") : bi_scope.

(** Verification of the template *)
Section One_Node_Template.

  Context {Σ} `{!heapG Σ, !onenodeG Σ} (N : namespace).
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
  
  Definition CSS γ_c C : iProp := 
    own γ_c (◯ (Excl' C)).
  
  Definition CSS_auth γ_c C : iProp := 
    own γ_c (● (Excl' C)).

  Definition css γ γ_c r : iProp :=
    ∃ (b: bool) (C: gset K),
      CSS_auth γ_c C
      ∗ γ ⤇½ C
      ∗ lockR b r (nodePred γ r).
        
  Definition css_inv γ γ_c r : iProp := inv N (css γ γ_c r).      

  Instance css_timeless γ γ_c r :
    Timeless (css γ γ_c r).
  Proof.
    rewrite /css. apply bi.exist_timeless; intros.
    apply bi.exist_timeless; intros.
    repeat apply bi.sep_timeless; try apply _.
    destruct x; try apply _.
  Qed.


  (** High-level lock specs **)

  Lemma lockNode_spec_high γ γ_c (r: Node) :
    ⊢  css_inv γ γ_c r -∗ 
        <<< True >>>
              lockNode #r @ ⊤ ∖ ↑N
        <<< nodePred γ r, RET #() >>>.
  Proof.
    iIntros "#Hcss" (Φ) "AU". 
    awp_apply (lockNode_spec r).
    iInv "Hcss" as ">H".
    iDestruct "H" as (b C)"(HC_auth & HC_frac & Hlock)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro. iFrame "AU".
      iNext. iExists b, C. iFrame.
    }
    iIntros "(Hlockn & Hnp)".
    iMod "AU" as "[_ [_ Hcomm]]".
    iMod ("Hcomm" with "Hnp") as "HΦ".
    iModIntro. iFrame "HΦ". 
    iNext. iExists true, C. iFrame.
  Qed.
  
  Lemma unlockNode_spec_high γ γ_c r :
    ⊢  css_inv γ γ_c r -∗ 
          nodePred γ r -∗ 
              <<< True >>>
              unlockNode #r @ ⊤ ∖ ↑N
            <<< True, RET #() >>>.
  Proof.
    iIntros "#Hcss Hnp" (Φ) "AU". 
    awp_apply (unlockNode_spec r).
    iInv "Hcss" as ">H".
    iDestruct "H" as (b C)"(HC_auth & HC_frac & Hlock)".
    iAssert (⌜b = true⌝)%I as "%".
    { destruct b; try done.
      iDestruct "Hlock" as "(_ & Hnp')".
      iDestruct "Hnp" as (Cn)"(node & _)".
      iDestruct "Hnp'" as (Cn')"(node' & _)".
      iExFalso; iApply (node_sep_star r); try iFrame. }
    subst b.      
    iCombine "Hlock Hnp" as "HlockR". 
    iAaccIntro with "HlockR".
    { iIntros "(Hlockn & Hnp)". iModIntro. iFrame.
      iNext. iExists true, C. iFrame. }
    iIntros "Hlockn".
    iMod "AU" as "[True [_ Hcomm]]".
    iMod ("Hcomm" with "True") as "HΦ".
    iModIntro. iFrame. 
    iExists false, C. iFrame.
  Qed.
  

  (** Proof of CSSOp *)
(*
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
*)

  Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.


  Theorem CSSOp_spec (γ γ_c: gname) r (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ 
        css_inv γ γ_c r -∗ 
            <<< ∀ C, CSS γ_c C >>>
              CSSOp dop r #k @ ⊤ ∖ ↑N
            <<< ∃ C' (res: bool), CSS γ_c C' ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "% #Hcss" (Φ) "AU". wp_lam. wp_bind(lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ γ_c r); try done.
    iAaccIntro with ""; try done.
    { iIntros "_". iModIntro. eauto with iFrame. }
    iIntros "Hnp". iModIntro. wp_pures.
    wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnp" as (C) "(node & Hfrac)".
    wp_apply ((decisiveOp_spec dop r k) with "[node]"). eauto with iFrame.
    iIntros (res C') "(node & %)".
    wp_pures.

    iApply fupd_wp.
    iInv "Hcss" as ">H".
    iDestruct "H" as (b C1)"(HC_auth & HC_frac & Hlock)".
    iMod "AU" as (C1')"[CSS [_ Hcomm]]".
    
    iDestruct (auth_agree with "HC_auth CSS") as %<-.
    iAssert (⌜C1 = C⌝)%I as "%".
    { iPoseProof (own_valid_2 _ _ _ with "[$Hfrac] [$HC_frac]") as "H'".
      iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
      destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
      by iPureIntro. } subst C1.

    iCombine "Hfrac HC_frac" as "H'". 
    iEval (rewrite <-frac_agree_op) in "H'". 
    iEval (rewrite Qp_half_half) in "H'".
    iMod ((own_update (γ) (to_frac_agree 1 C) 
                  (to_frac_agree 1 C')) with "[$H']") as "H'".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid_instance.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "H'".
    iEval (rewrite frac_agree_op) in "H'".  
    iDestruct "H'" as "(HC_frac & Hfrac)".
    iMod (auth_excl_update γ_c C' with "HC_auth CSS") as "[HC_auth CSS]".
    iMod ("Hcomm" $! C' res with "[CSS]") as "HΦ".
    { iFrame "∗%". }
    iModIntro. iSplitR "node Hfrac HΦ".
    iNext. iExists b, C'. iFrame.
    iModIntro.

    iAssert (nodePred γ r)%I with "[node Hfrac]" as "Hnp". 
    { iExists C'. iFrame. }
    awp_apply (unlockNode_spec_high with "[Hcss] [Hnp]") 
      without "HΦ"; try done.
    iAaccIntro with ""; try done.
    iIntros "_". iModIntro; iIntros "?". 
    wp_pures; eauto with iFrame.  
  Qed.

End One_Node_Template.

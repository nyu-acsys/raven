(** Verification of a simple example template: a two-node structure *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export inset_flows.
Require Import auth_ext search_str.

(** We use integers as keys. *)
Definition K := Z.


(** Definitions of cameras used in the template verification *)
Section Two_Node_Cameras.

  (* keyset RA *)
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

End Two_Node_Cameras.

(** Verification of the template *)
Section Two_Node_Template.

  Context `{!heapG Σ, !(@keysetG K _ _) Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. *)

  Parameter allocNodes : val.
  Parameter decisiveOp : (dOp → val).
  Parameter findNode : val.

  Definition create : val :=
    λ: <>,
      let: "(n1, n2)" := allocNodes #() in
      "(n1, n2)".

  Definition CSSOp (n1 n2: Node) (o: dOp) : val :=
    rec: "dictOp" "k" :=
      let: "n" := (findNode #n1 #n2 "k") in
      lockNode "n";;
      let: "res" := ((decisiveOp o) "n" "k") in
      unlockNode "n";;
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

  (* Predicate that defines the keyset of each node *)
  Parameter nodeKS : K → Node → Prop.
  
  Hypothesis nodeKS_sep_star: ∀ k n1 n2,
    n1 ≠ n2 → nodeKS k n1 → nodeKS k n2 → False.
  
  (** The concurrent search structure invariant *)

  Definition inFP (n1 n2 x: Node) : iProp :=
    ⌜x = n1 ∨ x = n2⌝.

  Definition nodePred γ n : iProp :=
    ∃ (Kn Cn: gset K),
      node n Cn
      ∗ own γ (◯ prod (Kn, Cn))
      ∗ ⌜∀ k: K, k ∈ KS → (k ∈ Kn ↔ nodeKS k n)⌝.

  Definition CSS γ n1 n2 (C: gset K) : iProp :=
    ∃ (b1 b2: bool),
      own γ (● prod (KS, C))
      ∗ lockR b1 n1 (nodePred γ n1)
      ∗ lockR b2 n2 (nodePred γ n2).

  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper *)

  Parameter allocNodes_spec :
      ⊢ ({{{ True }}}
           allocNodes #()
         {{{ (n1 n2: Node),
             RET (#n1, #n2); 
              node n1 ∅ ∗ (lockLoc n1) ↦ #false
            ∗ node n2 ∅ ∗ (lockLoc n2) ↦ #false  }}})%I.

  Parameter findNode_spec : ∀ (n1 n2: Node) (k: K),
      ⊢ ({{{ ⌜k ∈ KS⌝ }}}
           findNode #n1 #n2 #k
         {{{ (n: Node), RET #n; inFP n1 n2 n ∗ ⌜nodeKS k n⌝ }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n C }}}
           decisiveOp dop #n #k
         {{{ (res: bool) (C1: gset K),
             RET #res;
             node n C1 ∗ ⌜Ψ dop k C C1 res⌝ }}})%I.

  (** High-level lock specs **)

  Lemma lockNode_spec_high γ (n1 n2 n: Node) :
    ⊢  inFP n1 n2 n -∗
       <<< ∀ (C: gset K), CSS γ n1 n2 C >>>
         lockNode #n @ ⊤
       <<< CSS γ n1 n2 C ∗ nodePred γ n, RET #() >>>.
  Proof.
    iIntros "#Hfp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (b1 b2) "(HKS & Hlockr1 & Hlockr2)".
    iDestruct "Hfp" as "[%|%]".
    - (* n = n1 *)
      subst n.
      iAaccIntro with "Hlockr1".
      iIntros "Hlockrn". iModIntro.
      iFrame. iSplitL. iExists b1, b2.
      eauto with iFrame. iIntros "AU". iModIntro. iFrame.
      iIntros "(Hlockr1 & Hnp)". 
      iModIntro. iFrame. iSplitL. iExists true, b2. iFrame.
      iIntros. iModIntro. iFrame.

    - (* n = n2 *)
      subst n.
      iAaccIntro with "Hlockr2".
      iIntros "Hlockrn". iModIntro. iFrame. iSplitL.
      iExists b1, b2. eauto with iFrame.
      iIntros "AU". iModIntro. iFrame.
      iIntros "(Hlockn & Hnp)". iModIntro. iFrame.
      iSplitL. iFrame. iExists b1, true. iFrame.
      eauto with iFrame.
  Qed.
  
  Lemma unlockNode_spec_high γ (n1 n2 n: Node) :
    ⊢  inFP n1 n2 n -∗ 
        nodePred γ n -∗
        <<< ∀ (C: gset K), CSS γ n1 n2 C >>>
          unlockNode #n @ ⊤
       <<< CSS γ n1 n2 C, RET #() >>>.
  Proof.
    iIntros "HFP Hnp" (Φ) "AU". 
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (b1 b2) "(Keyset & Hl1 & Hl2)".
    iDestruct "HFP" as %HFP.
    destruct HFP as [? | ?]; subst n.
    - iAssert (⌜b1 = true⌝)%I as "%".
      { destruct b1; try done.
        iDestruct "Hl1" as "(_ & Hnp')".
        iDestruct "Hnp" as (Kn1 Cn1)"(node & _)".
        iDestruct "Hnp'" as (Kn1' Cn1')"(node' & _)".
        iExFalso; iApply (node_sep_star n1); try iFrame. }
      subst b1.      
      iCombine "Hl1 Hnp" as "HlockR". 
      iAaccIntro with "HlockR".
      { iIntros "(Hlockn & Hnp)". iModIntro. iSplitR "Hnp".
      iFrame. iExists true, b2. iFrame.
      iIntros "AU". iModIntro. iFrame.
      iPureIntro; left; try done. }
      iIntros "Hl1". iModIntro. 
      iSplitL. iExists false, b2. iFrame.
      eauto with iFrame. 
    - iAssert (⌜b2 = true⌝)%I as "%".
      { destruct b2; try done.
        iDestruct "Hl2" as "(_ & Hnp')".
        iDestruct "Hnp" as (Kn2 Cn2)"(node & _)".
        iDestruct "Hnp'" as (Kn2' Cn2')"(node' & _)".
        iExFalso; iApply (node_sep_star n2); try iFrame. }
      subst b2.      
      iCombine "Hl2 Hnp" as "HlockR". 
      iAaccIntro with "HlockR".
      { iIntros "(Hlockn & Hnp)". iModIntro. iSplitR "Hnp".
      iFrame. iExists b1, true. iFrame.
      iIntros "AU". iModIntro. iFrame.
      iPureIntro; right; try done. }
      iIntros "Hl2". iModIntro. 
      iSplitL. iExists b1, false. iFrame.
      eauto with iFrame. 
  Qed.
  

  (** Proof of CSSOp *)

  Theorem create_spec `{!∀ k n, Decision (nodeKS k n)}:
   ⊢ {{{ True }}}
        create #()
     {{{ γ (n1 n2: Node), RET (#n1, #n2); CSS γ n1 n2 ∅ }}}.
  Proof.
    iIntros (Φ). iModIntro.
    iIntros "_ HΦ". wp_lam. 
    wp_apply allocNodes_spec; try done.
    iIntros (n1 n2) "(node1 & Hl1 & node2 & Hl2)".
    iAssert (⌜n1 ≠ n2⌝)%I as "%".
    { destruct (decide (n1 = n2)); try done.
      subst n2. iExFalso. 
      iApply (node_sep_star n1); try iFrame. }
    rename H1 into n1_neq_n2. wp_pures.
    set (K1 := filter (λ k, nodeKS k n1) KS). 
    set (K2 := filter (λ k, nodeKS k n2) KS).
    iMod (own_alloc ((● prod (KS, ∅)) ⋅ (◯ (prod (K1, ∅)) ⋅ ◯ prod (K2, ∅)))) 
          as (γ)"Hg". 
    { rewrite <-auth_frag_op.
      rewrite auth_both_valid_discrete. split.
      - unfold op, cmra_op. simpl.
        unfold ucmra_op. simpl.
        destruct (decide (∅ ⊆ K1)); last try set_solver.
        destruct (decide (∅ ⊆ K2)); last try set_solver.
        destruct (decide (K1 ## K2)).
        + destruct (decide (∅ ## ∅)); last by set_solver.
          exists (prod (KS ∖ (K1 ∪ K2), ∅)).
          unfold op, cmra_op. simpl.
          destruct (decide (∅ ∪ ∅ ⊆ K1 ∪ K2)); last try set_solver.
          destruct (decide (∅ ⊆ KS ∖ (K1 ∪ K2))); last try set_solver.
          destruct (decide (K1 ∪ K2 ## KS ∖ (K1 ∪ K2))); last try set_solver.
          destruct (decide (∅ ∪ ∅ ## ∅)); last try set_solver.
          assert (KS = (K1 ∪ K2) ∪ KS ∖ (K1 ∪ K2)) as H'.
          { assert (K1 ⊆ KS) as H'. 
            { subst K1. intros k Hk. apply elem_of_filter in Hk.
              destruct Hk as [_ Hk]; try done. }
            assert (K2 ⊆ KS) as H''. 
            { subst K2. intros k Hk. apply elem_of_filter in Hk.
              destruct Hk as [_ Hk]; try done. }  
            clear -d H' H'' d1. apply leibniz_equiv. 
            rewrite set_equiv. intros k. split.
            * intros Hk. destruct (decide (k ∈ K1 ∪ K2)).
              ** set_solver.
              ** set_solver.
            * intros Hk. set_solver. }
          rewrite <-H'. repeat rewrite left_id_L. done.
        + exfalso. apply n. intros k HK1 HK2.
          apply (nodeKS_sep_star k n1 n2); try done.
          subst K1. apply elem_of_filter in HK1.
          destruct HK1 as [HK1 _]. done.
          subst K2. apply elem_of_filter in HK2.
          destruct HK2 as [HK2 _]. done.          
      - unfold valid, cmra_valid. simpl. unfold ucmra_valid. simpl.
        set_solver.      
    }
    iDestruct "Hg" as "(Hg● & Hg1 & Hg2)".
    iModIntro. iApply ("HΦ" $! γ n1 n2).
    iExists false, false. iFrame.
    iSplitL "node1 Hg1". iExists K1, ∅. iFrame.
    iPureIntro. subst K1. intros k HKS; split.
    intros Hk. apply elem_of_filter in Hk.
    destruct Hk as [Hk _]; try done.
    intros Hk. apply elem_of_filter. split; try done.
    iExists K2, ∅. iFrame.
    iPureIntro. subst K2. intros k HKS; split.
    intros Hk. apply elem_of_filter in Hk.
    destruct Hk as [Hk _]; try done.
    intros Hk. apply elem_of_filter. split; try done.
  Qed.


  Theorem CSSOp_spec (γ: gname) n1 n2 (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ n1 n2 C >>>
                          CSSOp n1 n2 dop #k @ ⊤
                 <<< ∃ C' (res: bool), CSS γ n1 n2 C'
                                     ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". wp_lam. wp_bind (findNode _ _ _)%E.
    wp_apply (findNode_spec n1 n2); first done.
    iIntros (n) "(#Hfp & %)". wp_pures. wp_bind (lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ n1 n2); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros "(HInv & Hnode)".
    (* Close AU and move on *)
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnode" as (Kn Cn) "(Hn & Hks & %)".
    wp_apply ((decisiveOp_spec dop n k) with "[Hn]"). eauto with iFrame.
    iIntros (res Cn') "(Hn & %)".
    wp_pures. wp_bind(unlockNode _)%E.
    awp_apply (unlockNode_spec_low).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C2) "HCss".

    (* Unfold CSS to execute unlockNode *)
    iDestruct "HCss" as (b1 b2) "(HKS & Hlockr1 & Hlockr2)".
    iDestruct "Hfp" as "[%|%]".
    - (* n = n1 *)
      subst n.
      iAssert (⌜b1 = true⌝)%I with "[-]" as "%".
      {
        destruct b1.
        - by iPureIntro.
        - iExFalso.
          iDestruct "Hlockr1" as "(? & Hn1)".
          iDestruct "Hn1" as (? ?) "(Hn1 & ?)".
          iApply (node_sep_star n1 with "[$]").
      }
      subst b1.
      iDestruct "Hlockr1" as "(Hl1 & _)".
      iAaccIntro with "Hl1".
      { iIntros "Hlock1". iModIntro.
        iFrame. iSplitL. iExists true, b2. iFrame.
        eauto with iFrame.
      }
      iIntros "Hlock1".
      (* Commit AU *)
      iMod ((ghost_update_keyset γ dop k Cn Cn' res Kn C2)
              with "[HKS Hks]") as (C2') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "Hks") as "%".
        assert (k ∈ Kn). by apply H2.
        assert (Cn' ⊆ Kn).
        { apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done. }
        iFrame "∗ #". by iPureIntro.
      }
      iModIntro.
      (* Close AU *)
      iExists C2', res. iSplitL. iSplitL.
      iExists false, b2.
      iFrame. iExists Kn, Cn'. iFrame. by iPureIntro. by iFrame.
      iIntros. iModIntro. by wp_pures.
    - (* n = n2. TODO can we refactor? *)
      subst n.
      iAssert (⌜b2 = true⌝)%I with "[-]" as "%".
      {
        destruct b2.
        - by iPureIntro.
        - iExFalso. 
        iDestruct "Hlockr2" as "(? & Hn2)".
        iDestruct "Hn2" as (? ?) "(Hn2 & ?)".
        iApply (node_sep_star n2 with "[$]").
      }
      subst b2.
      iDestruct "Hlockr2" as "(Hl2 & Hn2)".
      iAaccIntro with "Hl2".
      { iIntros "Hlock2". iModIntro.
        iFrame. iSplitL. iExists b1, true. iFrame.
        eauto with iFrame.
      }
      iIntros "Hlock2".
      (* Commit AU *)
      iMod ((ghost_update_keyset γ dop k Cn Cn' res Kn C2)
              with "[HKS Hks]") as (C2') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "Hks") as "%".
        assert (k ∈ Kn). by apply H2.
        assert (Cn' ⊆ Kn).
        { apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done. }
        iFrame "∗ #". by iPureIntro.
      }
      iModIntro.
      (* Close AU *)
      iExists C2', res. iSplitL. iSplitL.
      iExists b1, false.
      iFrame. iExists Kn, Cn'. iFrame. by iPureIntro. by iFrame.
      iIntros. iModIntro. by wp_pures.
  Qed.
  
End Two_Node_Template.

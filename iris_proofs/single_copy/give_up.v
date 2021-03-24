(** Verification of Give-up template algorithm *)

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
Require Import auth_ext.

(** We use integers as keys. *)
Definition K := Z.


(** Definitions of cameras used in the template verification *)
Section Give_Up_Cameras.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ :=
    FlowintG { flowint_inG :> inG Σ (authR (multiset_flowint_ur K)) }.
  Definition flowintΣ : gFunctors := #[GFunctor (authR (multiset_flowint_ur K))].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative sets of nodes *)
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.
  
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

End Give_Up_Cameras.

(** Verification of the template *)
Section Give_Up_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the give-up template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter allocRoot : val.
  Parameter findNext : val.
  Parameter inRange : val.
  Parameter decisiveOp : (dOp → val).

  Definition create : val :=
    λ: <>,
      let: "r" := allocRoot #() in
      "r".

  Definition traverse (r: Node) : val :=
    rec: "tr" "n" "k"  :=
      lockNode "n";;
      if: inRange "n" "k" then
        match: (findNext "n" "k") with
          NONE => "n"
        | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
        end
      else
        unlockNode "n";;
        "tr" #r "k".

  Definition CSSOp (Ψ: dOp) (r: Node) : val :=
    rec: "dictOp" "k" :=
      let: "n" := (traverse r) #r "k" in
      match: ((decisiveOp Ψ) "n" "k") with
        NONE => unlockNode "n";; "dictOp" "k"
      | SOME "res" => unlockNode "n";; "res"
      end.

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     b+-tree.spl and hashtbl-give-up.spl for the concrete definitions. *)
  Parameter node : Node → multiset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-give-up.spl and b+-tree.spl *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C',
    node n I_n C ∗ node n I_n' C' -∗ False.


  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper
   * (see b+-tree.spl and hashtbl-give-up.spl) *)

  Parameter allocRoot_spec :
      ⊢ ({{{ True }}}
           allocRoot #()
         {{{ (r: Node) (Ir: multiset_flowint_ur K) (ks: nzmap K nat),
             RET #r; node r Ir ∅ ∗ (lockLoc r) ↦ #false 
                     ∗ ⌜Ir = int {| infR := {[r := ks]}; outR := ∅ |}⌝
                     ∗ ⌜dom (gset K) ks = KS⌝
                     }}})%I.

  Parameter inRange_spec : ∀ (n: Node) (k: K) (In : multiset_flowint_ur K) (C: gset K),
   ⊢ ({{{ node n In C }}}
        inRange #n #k
      {{{ (res: bool), RET #res; node n In C ∗ ⌜res → in_inset K k In n⌝ }}})%I.

  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : multiset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ }}}
         findNext #n #k
       {{{ (succ: bool) (n': Node),
           RET (match succ with true => (SOMEV #n') | false => NONEV end);
           node n In C ∗ (match succ with true => ⌜in_outset K k In n'⌝ |
                                  false => ⌜¬in_outsets K k In⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (In: multiset_flowint_ur K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝
             ∗ ⌜¬in_outsets K k In⌝ }}}
           decisiveOp dop #n #k
         {{{ (succ: bool) (res: bool) (C1: gset K),
             RET (match succ with false => NONEV | true => (SOMEV #res) end);
             node n In C1 ∗ (match succ with false => ⌜C = C1⌝
                                        | true => ⌜Ψ dop k C C1 res⌝
                             end) }}})%I.

  (** The concurrent search structure invariant *)

  Definition inFP γ_f n : iProp := ∃ (N: gset Node), own γ_f (◯ N) ∗ ⌜n ∈ N⌝.

  Definition nodePred γ_I γ_k n In Cn  :iProp := 
                      node n In Cn 
                    ∗ own γ_k (◯ prod (keyset K In n, Cn))
                    ∗ own γ_I (◯ In) 
                    ∗ ⌜domm In = {[n]}⌝.

  Definition nodeFull γ_I γ_k n : iProp :=
    (∃ (b: bool) In Cn,
        lockR b n (nodePred γ_I γ_k n In Cn)).

  Definition globalGhost γ_I γ_f γ_k r C I : iProp :=
                    own γ_I (● I) 
                  ∗ ⌜globalinv K r I⌝ 
                  ∗ own γ_k (● prod (KS, C))
                  ∗ own γ_f (● domm I).

  Definition CSSi γ_I γ_f γ_k r C I : iProp :=
                    globalGhost γ_I γ_f γ_k r C I
                  ∗ ([∗ set] n ∈ (domm I), nodeFull γ_I γ_k n).

  Definition CSS γ_I γ_f γ_k r C : iProp := ∃ I, CSSi γ_I γ_f γ_k r C I.
    
  (** Some useful lemmas *)

  Lemma inFP_domm γ_I γ_f γ_k r C I n :
    inFP γ_f n -∗ CSSi γ_I γ_f γ_k r C I -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    iDestruct "Hfp" as (N) "(#Hdom' & n_in_N)". iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N) with "[$]") as "#N_incl".
    iDestruct "N_incl" as %N_incl.
    apply gset_included in N_incl.
    iPureIntro. set_solver.
  Qed.

  Lemma int_domm γ_I γ_f γ_k r C I n In :
    own γ_I (◯ In) -∗ ⌜domm In = {[n]}⌝ -∗ CSSi γ_I γ_f γ_k r C I -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "Hi Dom_In Hcss".
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    iPoseProof ((auth_own_incl γ_I (I) (In)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I.
    iPureIntro. rewrite I_incl. rewrite flowint_comp_fp.
    rewrite Dom_In. set_solver. rewrite <- I_incl.
    by apply auth_auth_valid. 
  Qed.
  
  Lemma CSS_unfold γ_I γ_f γ_k r C I n :
    CSSi γ_I γ_f γ_k r C I -∗ ⌜n ∈ domm I⌝ 
    -∗ (globalGhost γ_I γ_f γ_k r C I ∗ nodeFull γ_I γ_k n
        ∗ (∀ C',
           globalGhost γ_I γ_f γ_k r C' I ∗ nodeFull γ_I γ_k n
           -∗ CSS γ_I γ_f γ_k r C')).
  Proof.
    iIntros "Hcss %".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)". iFrame "∗".
    iIntros (C') "((HI & Hglob & Hks & Hdom) & H)".
    iExists I. iFrame "∗". by iApply "Hbigstar".
  Qed.

  Lemma node_nodeFull_equal γ_I γ_k n In Cn :
    node n In Cn -∗ nodeFull γ_I γ_k n
    -∗ ((lockR true n (∃ In Cn, nodePred γ_I γ_k n In Cn)) ∗(node n In Cn)).
  Proof.
    iIntros "Hn Hnf".
    iDestruct "Hnf" as (b In' Cn') "(Hlock & Hnp)". destruct b.
    - (* Case n locked *)
      iFrame "∗".
    - (* Case n unlocked: impossible *)
      iDestruct "Hnp" as "(Hn' & _)".
      iExFalso. iApply (node_sep_star n In In' with "[$]").
  Qed.

  Lemma CSS_unfold_node_wand γ_I γ_f γ_k r C I n In Cn :
    CSSi γ_I γ_f γ_k r C I
    -∗ node n In Cn -∗ ⌜n ∈ domm I⌝
    -∗ (node n In Cn
        ∗ globalGhost γ_I γ_f γ_k r C I
        ∗ (lockR true n (nodePred γ_I γ_k n In Cn))
        ∗ (∀ C',
           globalGhost γ_I γ_f γ_k r C' I ∗ nodeFull γ_I γ_k n
           -∗ CSS γ_I γ_f γ_k r C')).
  Proof.
    iIntros "Hcssi Hn %".
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iPoseProof (node_nodeFull_equal with "[$] [$]")
      as "(Hlock & Hn)".
    iFrame.
  Qed.

  Lemma ghost_snapshot_fp γ_f (Ns: gset Node) n:
    ⊢ own γ_f (● Ns) -∗ ⌜n ∈ Ns⌝ ==∗ own γ_f (● Ns) ∗ inFP γ_f n.
  Proof.
    iIntros. 
    iMod (own_update γ_f (● Ns) (● Ns ⋅ ◯ Ns) with "[$]")
      as "H".
    { apply auth_update_frac_alloc. apply gset_core_id. done. }
    iDestruct "H" as "(Haa & Haf)". iFrame. iModIntro.
    iExists Ns. by iFrame.
  Qed.

  (* ghost update for traverse inductive case *)
  Lemma ghost_update_step γ_I γ_f γ_k r C n In Cn k n' :
    ⊢ CSS γ_I γ_f γ_k r C
      -∗ nodePred γ_I γ_k n In Cn
      -∗ ⌜in_inset K k In n⌝
      -∗ ⌜in_outset K k In n'⌝
      ==∗ CSS γ_I γ_f γ_k r C ∗ nodePred γ_I γ_k n In Cn
      ∗ inFP γ_f n'.
  Proof.
    iIntros "Hcss Hnp % %".
    iDestruct "Hnp" as "(Hn & HkIn & HIn & %)".
    iDestruct "Hcss" as (I) "Hcssi".
    iPoseProof (int_domm with "[$] [% //] [$]") as "%".
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
    (* In ≼ I *)
    iPoseProof ((auth_own_incl γ_I I In) with "[$]")
      as (Io) "#incl".
    iDestruct "incl" as %incl. iDestruct "Hglob" as %Hglob.
    (* Some validities we'll use later *)
    iPoseProof (own_valid with "HI") as "%".
    iPoseProof (own_valid with "HIn") as "%".
    (* Prove the preconditions of ghost_snapshot_fp *)
    assert (n' ∈ domm Io). 
    { apply (flowint_step I In Io k n'); try done.
      rewrite auth_auth_valid in H4 *. trivial.
      unfold globalinv in Hglob.
      destruct Hglob as (_ & _ & cI & _). trivial. }
    assert (domm I = domm In ∪ domm Io). {
      rewrite incl. rewrite flowint_comp_fp. done.
      rewrite <- incl. by apply auth_auth_valid.
    }
    assert (n ∈ domm I). by set_solver.
    assert (n' ∈ domm I). by set_solver.
    (* Take snapshot of fp to get inFP n' *)
    iMod (ghost_snapshot_fp γ_f (domm I) n' with "[$Hdom] [% //]")
        as "(Hdom & #Hinfp')".
    iModIntro. iFrame "Hinfp'".
    iSplitL "Hcss' Hnf HI Hks Hdom". iApply "Hcss'". iFrame "∗ %".
    iFrame. iFrame "∗ %".
  Qed.

  (* root is in footprint *)
  Lemma ghost_update_root γ_I γ_f γ_k r C :
    ⊢ CSS γ_I γ_f γ_k r C
      ==∗ CSS γ_I γ_f γ_k r C ∗ inFP γ_f r.
  Proof.
    iIntros "Hcss". 
    (* Open CSS to get r ∈ domm I *)
    iDestruct "Hcss" as (I) "((HI & #Hglob & Hks & Hdom) & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    assert (r ∈ domm I)%I as Hroot.
    { apply globalinv_root_fp. done. }
    (* Snapshot FP for inFP: *)
    iMod (ghost_snapshot_fp γ_f (domm I) r with "[$Hdom] [% //]")
        as "(Hdom & #Hinfp)".
    iModIntro. iFrame "Hinfp".
    iExists I. iFrame "∗ %".
  Qed.

  (** High-level lock specs **)

  Lemma lockNode_spec_high γ_I γ_f γ_k r n :
    ⊢ inFP γ_f n
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k r C >>>
           lockNode #n @ ⊤
         <<< ∃ In Cn, CSS γ_I γ_f γ_k r C
                      ∗ nodePred γ_I γ_k n In Cn,
             RET #() >>>.
  Proof.
    iIntros "#HFp". iIntros (Φ) "AU". 
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (I) "Hcssi". 
    iPoseProof (inFP_domm with "[$] [$]") as "%". rename H0 into n_in_I.
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iSpecialize ("Hcss'" $! C).
    iDestruct "Hnf" as (b In Cn) "Hlock".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iPoseProof ("Hcss'" with "[-]") as "Hcss".
      { iFrame. iExists b, In, Cn. iFrame. }
      eauto with iFrame.
    }
    iIntros "Hlockn". iModIntro. 
    iDestruct "Hlockn" as "(Hlockn & Hnp)".
    iPoseProof ("Hcss'" with "[-Hnp]") as "Hcss".
    { iFrame. iExists true, In, Cn. iFrame. }
    iExists In, Cn. iSplitL. iSplitL "Hcss". iFrame. iFrame. eauto with iFrame.
  Qed.

  Lemma unlockNode_spec_high γ_I γ_f γ_k r n In Cn :
    ⊢ nodePred γ_I γ_k n In Cn
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k r C >>>
           unlockNode #n @ ⊤
         <<< CSS γ_I γ_f γ_k r C, RET #() >>>.
  Proof.
    iIntros "Hnp". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss". iDestruct "Hcss" as (I) "Hcss".
    iDestruct "Hnp" as "(Hnode & Hk & Hi & Dom_In)".
    iPoseProof (int_domm with "[$] [$] [$]") as "%".
    iPoseProof (CSS_unfold_node_wand with "[$] [$] [%]")
      as "(Hnode & Hg & Hlock & Hcss')"; try done.
    iAssert (nodePred γ_I γ_k n In Cn)%I 
        with "[Hnode Hk Hi Dom_In]" as "Hnp".
    { iFrame. }
    iCombine "Hlock Hnp" as "HPre".       
    iAaccIntro with "HPre".
    { iIntros "(Hlock & Hnp)". iModIntro.
      iPoseProof ("Hcss'" with "[-Hnp]") as "Hcss".
      { iFrame. iExists true, In, Cn. iFrame. }
      iFrame "Hcss". iIntros "AU". iModIntro.
      iSplitR "AU". iFrame "∗ #". done.
    }
    iIntros "Hlock". iModIntro.
    iPoseProof ("Hcss'" with "[-]") as "Hcss".
    { iFrame. iExists false. iFrame. iExists In, Cn. iFrame "∗ #". }
    eauto with iFrame.
 Qed.


  (** Proofs of traverse and CSSOp *)

  Theorem create_spec :
   ⊢ {{{ True }}}
        create #()
     {{{ γ_I γ_f γ_k (r: Node), RET #r; CSS γ_I γ_f γ_k r ∅ }}}.
  Proof.
    iIntros (Φ). iModIntro.
    iIntros "_ HΦ".
    wp_lam. wp_apply allocRoot_spec; try done.
    iIntros (r Ir ks) "(node & Hl & HIr & Hks)".
    iDestruct "HIr" as %HIr. iDestruct "Hks" as %Hks.
    iApply fupd_wp.
    iMod (own_alloc ( (● Ir) ⋅ (◯ Ir))) as (γ_I)"(HIr● & HIr◯)".
    { apply auth_both_valid_discrete. split; try done.
      unfold valid, cmra_valid. simpl. unfold ucmra_valid.
      simpl. unfold flowint_valid. subst Ir.
      split; try done. apply map_disjoint_dom. set_solver. }
    iMod (own_alloc ((● prod (KS, ∅)) ⋅ (◯ (prod (KS, ∅))))) 
          as (γ_k)"(Hks● & Hks◯)".
    { apply auth_both_valid_discrete. split; try done. }
    iMod (own_alloc (● (domm Ir))) 
          as (γ_f)"Hf". { apply auth_auth_valid. try done. }
    iModIntro. wp_pures.
    iModIntro. iApply ("HΦ" $! γ_I γ_f γ_k r).
    iExists Ir. iFrame. iSplitR.
    - iPureIntro. repeat split; try done.
      unfold valid, cmra_valid, flowint_valid.
      subst Ir; split; try done.
      apply map_disjoint_dom; set_solver.
      subst Ir. unfold domm, dom, flowint_dom. simpl.
      rewrite dom_singleton. set_solver.
      unfold closed, outset, dom_ms, out, out_map.
      subst Ir; simpl. try done.
      unfold inset, dom_ms, inf.
      subst Ir; simpl. rewrite lookup_singleton; simpl.
      intros k Hk; rewrite Hks; try done.
    - assert (domm Ir = {[r]}) as Domm_Ir.
      { subst Ir; unfold domm, dom, flowint_dom, inf_map; simpl.
        apply leibniz_equiv. by rewrite dom_singleton. }
      rewrite Domm_Ir. rewrite big_opS_singleton.
      iExists false, Ir, ∅. iFrame "∗%".
      assert (keyset K Ir r = KS) as Hkeyset.
      { unfold keyset. unfold dom_ms, inf, out; subst Ir; simpl.
        rewrite nzmap_lookup_empty. rewrite lookup_singleton.
        unfold ccmunit at 2. unfold ccm_unit. simpl.
        unfold nzmap_dom. simpl.
        assert (dom (gset K) (∅: gmap K nat) = ∅) as H'.
        { apply leibniz_equiv. by rewrite dom_empty. }
        rewrite H' Hks. set_solver. }
      by rewrite Hkeyset.   
  Qed.     


  Lemma traverse_spec (γ_I γ_f γ_k: gname) (k: K) (r n: Node):
   ⊢ ⌜k ∈ KS⌝ ∗ inFP γ_f n -∗
     <<< ∀ C, CSS γ_I γ_f γ_k r C >>>
       traverse r #n #k @ ⊤
     <<< ∃ (n': Node) (I_n': multiset_flowint_ur K) (C_n': gset K),
          CSS γ_I γ_f γ_k r C
        ∗ nodePred γ_I γ_k n' I_n' C_n' 
        ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n). iIntros "(#Hks & #Hfp)".
    iDestruct "Hks" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ_I γ_f γ_k r n); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros (In Cn) "(HInv & Nodepred)".
    (* Close AU and move on *)
    iModIntro. iFrame. iIntros "AU". iModIntro.
    wp_pures. wp_bind (inRange _ _)%E.
    iDestruct "Nodepred" as "(Hnode & H◯k & H◯I & Dom_In)".
    wp_apply ((inRange_spec n k In Cn) with "Hnode").
    iIntros (b) "(Hnode & Hb)". destruct b.
    - (* Case : inRange returns true *)
      wp_pures. wp_bind (findNext _ _)%E. iSimpl in "Hb".
      iDestruct "Hb" as %Hinset. specialize (Hinset Coq.Init.Logic.I).
      wp_apply ((findNext_spec n k In Cn) with "[Hnode]"). iFrame "∗ %".
      iIntros (b n') "(Hnode & Hbb)". destruct b.
      + (* Case : findNext returns Some n' *)
        wp_pures. iDestruct "Hbb" as %in_outset.
        (* Get CSS from AU to step to n' *)
        iApply fupd_wp. iMod "AU" as (C) "[Hcss [Hclose _]]".
        iAssert (nodePred γ_I γ_k n In Cn)%I 
                        with "[H◯k H◯I Dom_In Hnode]" as "Hn". by iFrame.
        (* ghost update to step to n' *)                
        iMod (ghost_update_step with "[$] [$] [% //] [% //]") as "(Hcss & Hnp & #Hinfp')".
        (* Close AU *)
        iMod ("Hclose" with "Hcss") as "AU". iModIntro.
        (* Unlock node n *)
        awp_apply ((unlockNode_spec_high γ_I γ_f γ_k r n) with "[-AU //]").
        iApply (aacc_aupd_abort with "AU"); first done.
        iIntros (C2) "HInv". iAaccIntro with "HInv".
        { iIntros "HInv". iModIntro. eauto with iFrame. }
        iIntros "HInv". iModIntro. iFrame. iIntros "AU".
        iModIntro. wp_pures.
        (* Apply induction hypothesis on n' *) 
        iApply "IH"; try done. iFrame "% #".
      + (* Case : findNext returns None *)
        iDestruct "Hbb" as %not_in_outset.
        (* Open AU and commit *)
        iApply fupd_wp. iMod "AU" as (C) "[HInv [_ Hclose]]".
        iSpecialize ("Hclose" $! n In Cn).
        iDestruct "Dom_In" as "%".
        iMod ("Hclose" with "[H◯k H◯I HInv Hnode]").
        iFrame "∗ # %". iModIntro. wp_pures. done.
    - (* Case : inRange returns false *)
      wp_pures. iDestruct "Hb" as %Hnot_in_inset.
      (* Unlock node n *)
      awp_apply ((unlockNode_spec_high γ_I γ_f γ_k r n) with "[-AU]").
      iFrame "∗ # %". iApply (aacc_aupd_abort with "AU"); first done.
      iIntros (C) "HInv". iAaccIntro with "HInv".
      { iIntros. iModIntro. eauto with iFrame. }
      iIntros "HInv".
      (* Get pre of inductive hypothesis with root before closing AU *)
      iMod (ghost_update_root with "[$]") as "(HInv & #HinFPr)".
      iModIntro. iFrame. iIntros "AU".
      iModIntro. wp_pures.
      (* Apply induction hypothesis on root *)
      iApply "IH"; try done. iFrame "% #".
  Qed.

  (** Verification of abstract specification of the search structure operation. *)
  
  Theorem CSSOp_spec (γ_I γ_f γ_k: gname) r (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ_I γ_f γ_k r C >>>
                          CSSOp dop r #k @ ⊤
                 <<< ∃ C' (res: bool), CSS γ_I γ_f γ_k r C'
                                     ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iDestruct "HKin" as %k_in_KS.
    (* Open AU and get pre for traverse_spec *)
    iApply fupd_wp. iMod "AU" as (C0) "[HInv [HAU _]]".
    iMod (ghost_update_root with "[$]") as "(HInv & #HinFPr)".
    (* Close AU *)
    iMod ("HAU" with "HInv") as "AU". iModIntro.
    (* Open AU and apply traverse_spec *)
    awp_apply (traverse_spec γ_I γ_f γ_k k r r); first by iFrame "% #".
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "HInv". iAaccIntro with "HInv"; first by eauto with iFrame.
    (* traverse returns node n and it's local ghost state *)
    iIntros (n In Cn) "(HInv & Nodepred & % & %)".
    rename H0 into in_inset. rename H1 into not_in_outset.
    (* Close AU and move on *) 
    iModIntro. iFrame. iIntros "AU".
    iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Nodepred" as "(Hnode & Hk & Hi & Dom_In)".
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hnode]"). eauto with iFrame.
    iIntros (b res Cn'). iIntros "(Hnode & Hb)". destruct b.
    - (* Case : decisiveOp succeeds *)
      iDestruct "Hb" as "#HΨ".
      wp_pures. wp_bind(unlockNode _)%E.
      (* Note: cannot use unlockNode_spec_high here because 
         that needs nodePred, which we won't have until we linearize,
         which we can't do until we open the AU.
         We can't open the AU before unlockNode, because linearizing will
         mean committing the AU and giving up CSS (needed by unlockNode).
         So we manually execute unlockNode_spec and linearize simultaneously.
       *)      
      awp_apply (unlockNode_spec_low n).
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (C2) "HInv". iDestruct "HInv" as (I2)"HInv".
      (* Unfold CSS to execute unlockNode *)
      iPoseProof (int_domm with "[$] [$] [$]") as "%".      
      iPoseProof (CSS_unfold_node_wand with "[$] [$] [%]")
        as "(Hn & Hg & Hlock & Hcss')"; try done.
      iDestruct "Hlock" as "(Hlock & _)".
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro.
        iPoseProof ("Hcss'" with "[-Hn Hk Hi Dom_In]") as "Hcss".
        { iFrame. iExists true, In, Cn. iFrame. }
        iFrame "Hcss". iIntros "AU". iModIntro. iFrame.
      }
      iIntros "Hlock".
      (* Commit AU *)
      iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2)
              with "[Hk Hks]") as (C2') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "Hk") as "%".
        assert (k ∈ keyset K In n); first by apply keyset_def.
        iAssert (⌜Cn' ⊆ keyset K In n⌝)%I with "[HΨ]" as "%".
        { iDestruct "HΨ" as "%". iPureIntro.
          apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done.
        }
        iFrame "∗ #". by iPureIntro.
      }
      iModIntro.
      (* Close AU *)
      iExists C2', res. iSplitL. iFrame "HΨC".
      iApply "Hcss'". iFrame "∗ % #". iExists false. iFrame "∗ # %".
      iExists In, Cn'. iFrame. iIntros. iModIntro. by wp_pures. 
    - (* Case : decisiveOp fails *) 
      wp_match. iDestruct "Hb" as "%". subst Cn'.
      (* Open AU and apply unlockNode spec *)
      awp_apply ((unlockNode_spec_high γ_I γ_f γ_k r n) with "[-AU]").
      iFrame. iApply (aacc_aupd_abort with "AU"); first done.
      iIntros (C2) "HInv".
      (* execute unlockNode and close AU *)
      iAaccIntro with "HInv"; try 
        iIntros "HInv"; iModIntro; iFrame; iIntros; iModIntro; try done.     
      wp_pures.
      (* Apply induction hypothesis *)
      iApply "IH"; try done.
  Qed.      

End Give_Up_Template.

(** Verification of lock coupling template algorithm *)

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
Section Coupling_Cameras.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ :=
    FlowintG { flowint_inG :> inG Σ (authR (multiset_flowint_ur K)) }.
  Definition flowintΣ : gFunctors := #[GFunctor (authR (multiset_flowint_ur K))].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative set of nodes *)
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  (* RA for pair of keysets and contents *)
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

  (* RA for set of contents *)
  Class contentG Σ :=
    ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR K)))) }.
  Definition contentΣ : gFunctors :=
    #[GFunctor (authR (optionUR (exclR (gsetR K))))].

End Coupling_Cameras.

(** Verification of the template *)
Section Coupling_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (** The code of the coupling template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter allocRoot : val.
  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).
  Parameter alloc : val.

  Definition create : val :=
    λ: <>,
      let: "r" := allocRoot #() in
      "r".

  Definition traverse : val :=
    rec: "tr" "p" "n" "k" :=
      match: Fst (findNext "n" "k") with
        NONE => (("p", "n"), Snd (findNext "n" "k"))
      | SOME "n'" =>
        lockNode "n'";; unlockNode "p";; "tr" "n" "n'" "k"
      end.

  Definition CSS_insertOp (root: Node) : val :=
    λ: "k",
    lockNode #root;;
    let: "n0" := Fst (findNext #root "k") in
    match: "n0" with
      NONE => ""
    | SOME "n0" =>
      lockNode "n0";;
      let: "tr_res" := traverse #root "n0" "k" in
      let: "b" := Snd "tr_res" in
      if: "b" then
        #false
      else
        let: "pn" := Fst "tr_res" in
        let: "p" := Fst "pn" in
        let: "n" := Snd "pn" in
        let: "m" := alloc #() in
        let: "res" := (decisiveOp insertOp) "p" "n" "k" in
        unlockNode "p";; unlockNode "n";; "res" end.

  (** Assumptions on the implementation made by the template proofs.
   * Matching definitions can be found in GRASShopper file list-coupling.spl *)

  (* The node predicate is specific to each template implementation. *)
  Parameter node : Node → Node → multiset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * root-order separation logic. *)
  Parameter node_timeless_proof : ∀ root n I C, Timeless (node root n I C).
  Instance node_timeless root n I C: Timeless (node root n I C).
  Proof. apply node_timeless_proof. Qed.

  (* Spatial part of node predicate. *)
  Parameter hrepSpatial : Node → iProp.

  (* The node-local invariant.
   * See list-coupling.spl for the corresponding GRASShopper definition.*)
  (* TODO there's a slight discrepancy between this and grasshopper. *)
  Definition nodeinv root n (In : multiset_flowint_ur K) Cn : Prop :=
    domm In = {[n]}
    ∧ Cn ⊆ keyset K In n
    ∧ (∀ k : K, default 0 (inf In n !! k) ≤ 1)
    ∧ (n = root → ∀ k1 : K, k1 ∈ KS → in_outsets K k1 In).

  (* The following hypotheses are proved as GRASShopper lemmas in
   * list-coupling.spl *)
  Hypothesis node_implies_nodeinv : ∀ root n In C,
    ⌜✓In⌝ -∗ node root n In C -∗ ⌜nodeinv root n In C⌝.

  Hypothesis node_sep_star: ∀ root n In In' C C',
    node root n In C -∗ node root n In' C' -∗ False.

  Lemma successor_not_root : ∀ (I I1 I2 I3 : flowintT) C root n k,
      globalinv K root I →
      I = I1 ⋅ I2 ⋅ I3 →
      k ∈ outset K I1 n →
      k ∈ KS →
      nodeinv root n I2 C →
      n ≠ root.
  Proof.
    intros ? ? ? ? ? ? ? ? GI IDef k_in_out1 k_in_KS NI.
    destruct (decide (n = root)).
    destruct GI as (VI & root_in_I & I_closed & I_inf_out).
    rewrite <- cmra_assoc in IDef.
    (*unfold op, cmra_op, ucmra_cmraR, multiset_flowint_ur, flowintUR, ucmra_op in IDef.*)
    rewrite IDef in VI.
    pose proof (intComp_valid_proj1 _ _ VI) as V1.
    pose proof (intComp_valid_proj2 _ _ VI) as V23.
    pose proof (intComp_unfold_inf_1 _ _ VI n) as inf_I1.
    pose proof (intComp_unfold_inf_1 _ _ V23) as inf_I2.
    destruct NI as (domm_I2 & _ & inf_bound & _).
    assert (n ∈ domm I2 ∪ domm I3) as n_in_I23 by set_solver.
    pose proof (intComp_unfold_inf_2 _ _ VI n) as inf_I23.
    rewrite intComp_dom in inf_I23.
    apply inf_I23 in n_in_I23 as n_inf_I23.
    unfold cmra_op, flowintRA, cmra_car, K_multiset at 5, K_multiset at 5 in n_inf_I23.
    pose proof (I_inf_out k k_in_KS) as root_out_k.
    assert (default 0 (inf I n !! k) ≠ 0).
    rewrite e.
    unfold inset, dom_ms in root_out_k.
    apply nzmap_elem_of_dom in root_out_k.
    unfold lookup, nzmap_lookup.
    pose proof (nzmap_is_wf (inf I root)) as inf_root_wf.
    pose proof (nzmap_lookup_wf _ k inf_root_wf).
    destruct (inf I root).
    simpl in root_out_k.
    unfold is_Some in root_out_k.
    destruct root_out_k as [x root_out_k].
    unfold lookup, nzmap_lookup in root_out_k.
    rewrite root_out_k.
    simpl in H0.
    simpl.
    naive_solver.
    pose proof (lookup_op _ _ (inf I n) (out I1 n) k) as inf_I23_def.

    rewrite IDef in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I23_def.
    unfold ccm_op, lift_ccm in n_inf_I23.

    unfold K_multiset_ccm at 4, lift_ccm in n_inf_I23.
    rewrite <- n_inf_I23 in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car in IDef.
    rewrite <- IDef in inf_I23_def.

    assert (n ∈ domm I2) as n_in_I2 by set_solver.
    pose proof (inf_I2 n n_in_I2) as n_inf_I2.
    pose proof (lookup_op _ _ (inf (I2 ⋅ I3) n) (out I3 n) k) as inf_I2_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I2_def.
    unfold K_multiset_ccm, ccmop, ccm_op, lift_ccm in n_inf_I2.
    setoid_rewrite <- n_inf_I2 in inf_I2_def.
    setoid_rewrite inf_I23_def in inf_I2_def.

    assert (default 0 (out I1 n !! k) ≠ 0).
    unfold outset, dom_ms in k_in_out1.
    apply nzmap_elem_of_dom in k_in_out1.
    pose proof (nzmap_is_wf (out I1 n)) as out_n_wf.
    pose proof (nzmap_lookup_wf _ k out_n_wf).
    destruct (out I1 n).
    simpl in k_in_out1.
    unfold is_Some in k_in_out1.
    destruct k_in_out1 as [x k_in_out1].
    rewrite k_in_out1.
    simpl in H0.
    simpl.
    naive_solver.
    unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I23_def.
    unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I2_def.
    pose proof (inf_bound k).
    remember (inf I2 n !! k) as x2.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx2.
    setoid_rewrite <- Heqx2 in inf_I2_def.
    remember (inf I n !! k) as x.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx.
    rewrite <- Heqx in inf_I2_def.
    remember (out I1 n !! k) as x1.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx1.
    rewrite <- Heqx1 in inf_I2_def.
    lia.
    all: trivial.
  Qed.


  (** Helper functions specs *)

  (* The following functions are proved for each implementation in GRASShopper
   * (see list-coupling.spl) *)

  Parameter allocRoot_spec :
      ⊢ ({{{ True }}}
           allocRoot #()
         {{{ (r: Node) (Ir: multiset_flowint_ur K) (ks: nzmap K nat),
             RET #r; node r r Ir ∅ ∗ (lockLoc r) ↦ #false 
                     ∗ ⌜Ir = int {| infR := {[r := ks]}; outR := ∅ |}⌝
                     ∗ ⌜dom (gset K) ks = KS⌝
                     }}})%I.

  (* TODO ghp spec doesn't match *)
  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : multiset_flowint_ur K) (C: gset K) root,
     ⊢ ({{{ node root n In C ∗ ⌜in_inset K k In n⌝ }}}
           findNext #n #k
       {{{ (succ: bool) (np: Node) (res: bool),
              RET (match succ with true => ((SOMEV #np), #res) | false => (NONEV, #res) end);
                  node root n In C ∗ ⌜res ↔ k ∈ C⌝
               ∗ (match succ with true  => ⌜in_outset K k In np⌝
                                | false => ⌜¬in_outsets K k In⌝ ∗ ⌜n ≠ root⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec : ∀ root (p n m: Node) (k: K) (Ip In: multiset_flowint_ur K) (Cp Cn: gset K),
     ⊢ ({{{       ⌜k ∈ KS⌝
                ∗ ⌜keyset K Ip p ## keyset K In n⌝
                ∗ node root p Ip Cp
                ∗ node root n In Cn
                ∗ hrepSpatial m
                ∗ ⌜✓ (Ip ⋅ In)⌝
                ∗ ⌜out (Ip ⋅ In) m = 0%CCM⌝
                ∗ ⌜m ≠ root⌝
                ∗ ⌜n ≠ root⌝
                ∗ ⌜k ∉ Cn⌝
                ∗ ⌜in_outset K k Ip n⌝
                ∗ ⌜in_inset K k Ip p⌝
                ∗ ⌜¬in_outsets K k In⌝ }}}

           decisiveOp insertOp #p #n #k

       {{{ (Cp1 Cn1 Cm1: gset K) (Ip1 In1 Im1: flowintUR K_multiset) (res: bool), RET  #res;
                  node root p Ip1 Cp1
                ∗ node root n In1 Cn1
                ∗ node root m Im1 Cm1
                ∗ ⌜Ψ insertOp k (Cp ∪ Cn) (Cp1 ∪ Cn1 ∪ Cm1) res⌝
                ∗ ⌜contextualLeq _ (Ip ⋅ In) (Ip1 ⋅ In1 ⋅ Im1)⌝
                ∗ ⌜inf (Ip1 ⋅ In1 ⋅ Im1) m = 0%CCM⌝
                ∗ ⌜keyset K Ip1 p ## keyset K In1 n⌝
                ∗ ⌜keyset K Ip1 p ## keyset K Im1 m⌝
                ∗ ⌜keyset K Im1 m ## keyset K In1 n⌝
                ∗ ⌜keyset K Ip1 p ∪ keyset K In1 n ∪ keyset K Im1 m = keyset K Ip p ∪ keyset K In n⌝ }}})%I.

  (*TODO changed back to original spec*)
  Parameter alloc_spec :
     ⊢ ({{{ True }}}
           alloc #()
       {{{ (m: Node) (l:loc), RET #m; hrepSpatial m ∗ ⌜lockLoc m = l⌝ ∗ l ↦ #false }}})%I.


  (** The concurrent search structure invariant *)

  Definition inFP γ_f n : iProp := ∃ (N: gset Node), own γ_f (◯ N) ∗ ⌜n ∈ N⌝.

  Definition nodePred γ_I γ_k root n In Cn  :iProp :=
                      node root n In Cn
                    ∗ own γ_k (◯ prod (keyset K In n, Cn))
                    ∗ own γ_I (◯ In)
                    ∗ ⌜domm In = {[n]}⌝.

  Definition nodeFull γ_I γ_k root n : iProp :=
    (∃ (b: bool) In Cn,
        (lockR b n (nodePred γ_I γ_k root n In Cn))).

  Definition globalGhost γ_I γ_f γ_k γ_c root I C : iProp :=
                    own γ_I (● I)
                  ∗ ⌜globalinv K root I⌝
                  ∗ own γ_k (● prod (KS, C))
                  ∗ own γ_f (● domm I)
                  ∗ own γ_c (● (Some (Excl C))).

  Definition CSSi γ_I γ_f γ_k γ_c root I C : iProp :=
                    globalGhost γ_I γ_f γ_k γ_c root I C
                  ∗ ([∗ set] n ∈ (domm I), nodeFull γ_I γ_k root n).

  Definition CSS γ_I γ_f γ_k γ_c root : iProp := ∃ I C, CSSi γ_I γ_f γ_k γ_c root I C.

  Definition css_inv γ_I γ_f γ_k γ_c root : iProp := inv N (CSS γ_I γ_f γ_k γ_c root).

  Definition css_cont (γ_c: gname) (C: gset K) : iProp := own γ_c (◯ (Excl' C)).

  Instance CSS_timeless  γ_I γ_f γ_k γ_c root :
    Timeless (CSS γ_I γ_f γ_k γ_c root).
  Proof.
    rewrite /CSS. apply bi.exist_timeless; intros.
    apply bi.exist_timeless; intros.
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless.
    intros. apply bi.exist_timeless. intros.
    apply bi.exist_timeless. intros.
    apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x2; try apply _.
  Qed.

  (** Some useful lemmas *)

  Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.


  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P K_multiset I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq K_multiset I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro. destruct x.
      simpl in Hx. simpl in HIn.
      rewrite Hx. rewrite <-HIn.
      rewrite Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (1%Qp, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n'). unfold cmra_op.
        simpl. unfold view_op_instance. simpl.
        assert (ε ⋅ I_n' = I_n') as H'. by rewrite left_id.
        rewrite H'. unfold op, cmra_op. by simpl. }   
      by iEval (rewrite H').
  Qed.

  Lemma inFP_domm γ_I γ_f γ_k γ_c root I C n  :
    inFP γ_f n -∗ CSSi γ_I γ_f γ_k γ_c root I C -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
    iDestruct "Hfp" as (N0) "(#Hdom' & n_in_N)". iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N0) with "[$]") as "#N_incl".
    iDestruct "N_incl" as %N_incl.
    apply gset_included in N_incl.
    iPureIntro. set_solver.
  Qed.

  Lemma int_domm γ_I γ_f γ_k γ_c root I C n In :
    own γ_I (◯ In) -∗ ⌜domm In = {[n]}⌝ -∗ CSSi γ_I γ_f γ_k γ_c root I C -∗ ⌜n ∈ domm I⌝.
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

  Lemma node_nodeFull_equal γ_I γ_k root n In Cn :
    node root n In Cn -∗ nodeFull γ_I γ_k root n
    -∗ ((lockR true n (∃ In Cn, nodePred γ_I γ_k root n In Cn))∗ (node root n In Cn)).
  Proof.
    iIntros "Hn Hnf".
    iDestruct "Hnf" as (b In' Cn') "(Hlock & Hnp)". destruct b.
    - (* Case n locked *)
      iFrame "∗".
    - (* Case n unlocked: impossible *)
      iDestruct "Hnp" as "(Hn' & _)".
      iExFalso. iApply (node_sep_star root n In In' with "[$] [$]").
  Qed.

  Lemma CSS_unfold γ_I γ_f γ_k γ_c root I C n :
    CSSi γ_I γ_f γ_k γ_c root I C -∗ ⌜n ∈ domm I⌝
    -∗ (globalGhost γ_I γ_f γ_k γ_c root I C ∗ nodeFull γ_I γ_k root n
        ∗ (∀ C',
           globalGhost γ_I γ_f γ_k γ_c root I C' ∗ nodeFull γ_I γ_k root n
           -∗ CSSi γ_I γ_f γ_k γ_c root I C')).
  Proof.
    iIntros "Hcss %".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)". iFrame "∗".
    iIntros (C') "((HI & Hglob & Hks & Hdom) & H)".
    iFrame "∗". by iApply "Hbigstar".
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

  (* root is in footprint *)
  Lemma ghost_update_root γ_I γ_f γ_k γ_c root :
    ⊢ CSS γ_I γ_f γ_k γ_c root
      ==∗ CSS γ_I γ_f γ_k γ_c root ∗ inFP γ_f root.
  Proof.
    iIntros "Hcss".
    (* Open CSS to get r ∈ domm I *)
    iDestruct "Hcss" as (I C) "((HI & #Hglob & Hks & Hdom & Hcont) & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    assert (root ∈ domm I)%I as Hroot.
    { apply globalinv_root_fp. done. }
    (* Snapshot FP for inFP: *)
    iMod (ghost_snapshot_fp γ_f (domm I) root with "[$Hdom] [% //]")
        as "(Hdom & #Hinfp)".
    iModIntro. iFrame "Hinfp".
    iExists I, C. iFrame "∗ %".
  Qed.

  Lemma Ψ_key_present γ_k k n In (Cn C: gset K) :
        ⌜true ↔ k ∈ Cn⌝ -∗ own γ_k (● prod (KS, C))
                        -∗ own γ_k (◯ prod (keyset K In n, Cn))
                        -∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (keyset K In n, Cn))
                                                    ∗ ⌜Ψ insertOp k C C false⌝.
  Proof.
    iIntros "H Hks Hkn". iDestruct "H" as %Hres.
    iPoseProof (own_valid with "Hks") as "%". rename H0 into Valid_ks_auth.
    iPoseProof (own_valid with "Hkn") as "%". rename H0 into Valid_ks_frag.
    iPoseProof ((auth_own_incl γ_k (prod (KS, C)) _) with "[Hks Hkn]") as "%".
    iFrame. rename H0 into ks_incl.
    rewrite auth_auth_valid in Valid_ks_auth *; intros Valid_ks_auth.
    rewrite auth_frag_valid in Valid_ks_frag *; intros Valid_ks_frag.
    pose proof (auth_ks_included (keyset K In n) KS Cn C Valid_ks_frag Valid_ks_auth ks_incl)
                               as ks_incl_lemma.
    iFrame. unfold Ψ. iPureIntro.
    assert (k ∈ Cn). by apply Hres.
    destruct ks_incl_lemma.
    - destruct H1. subst C.
      split; set_solver.
    - destruct H1 as [a [b [_ [H1 _]]]].
      split; set_solver.
  Qed.

 (* TODO had to change to original implementation using lockLoc for now *)
  Lemma node_lock_not_in_FP γ_I γ_f γ_k γ_c root I C n b :
  lockLoc n ↦ #b -∗ CSSi γ_I γ_f γ_k γ_c root I C -∗ ⌜n ∉ domm I⌝.
  Proof.
    iIntros "Hl Hcss". iDestruct "Hcss" as "(Hg & Hbigstar)".
    destruct (decide (n ∈ domm I)).
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)". 
    iDestruct "Hn" as (b0 In Cn) "(Hlockn & Hb)".
    iDestruct (mapsto_valid_2 with "Hl Hlockn") as "%". 
    exfalso. destruct H0. by compute in H0.
    by iPureIntro.
  Qed.

  Lemma CSS_unfold_node_wand γ_I γ_f γ_k γ_c root I C n In Cn :
    CSSi γ_I γ_f γ_k γ_c root I C
    -∗ node root n In Cn -∗ ⌜n ∈ domm I⌝
    -∗ (node root n In Cn
        ∗ globalGhost γ_I γ_f γ_k γ_c root I C
        ∗ (lockR true n (nodePred γ_I γ_k root n In Cn))
        ∗ (∀ C',
           globalGhost γ_I γ_f γ_k γ_c root I C' ∗ nodeFull γ_I γ_k root n
           -∗ CSSi γ_I γ_f γ_k γ_c root I C')).
  Proof.
    iIntros "Hcssi Hn %".
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iPoseProof (node_nodeFull_equal with "[$] [$]")
      as "(Hlock & Hn)".
    iFrame.
  Qed.


  (* ghost update for traverse inductive case *)
  Lemma ghost_update_step γ_I γ_f γ_k γ_c root n In Cn k n' :
    ⊢ CSS γ_I γ_f γ_k γ_c root
      -∗ nodePred γ_I γ_k root n In Cn
      -∗ ⌜in_inset K k In n⌝
      -∗ ⌜in_outset K k In n'⌝
      ==∗ CSS γ_I γ_f γ_k γ_c root ∗ nodePred γ_I γ_k root n In Cn
      ∗ inFP γ_f n'.
  Proof.
    iIntros "Hcss Hnp % %".
    iDestruct "Hnp" as "(Hn & HkIn & HIn & %)".
    iDestruct "Hcss" as (I C) "Hcssi".
    iPoseProof (int_domm with "[$] [% //] [$]") as "%".
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iDestruct "Hg" as "(HI & Hglob & Hks & Hdom & Hc)".
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
      rewrite auth_auth_valid in H4 *. done.
      unfold globalinv in Hglob.
      destruct Hglob as (_ & _ & cI & _). done.
    }
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
    iSplitL "Hcss' Hnf HI Hks Hdom Hc". iExists I, C.
    iApply "Hcss'". iFrame "∗ %".
    iFrame. iFrame "∗ %".
  Qed.


  Lemma extract_from_nodeinv root p Ip Cp :
        ⌜✓ Ip⌝ -∗ node root p Ip Cp -∗ ⌜Cp ⊆ keyset K Ip p ∧ domm Ip = {[p]}⌝.
  Proof.
    iIntros "% Hnode".
    iPoseProof (node_implies_nodeinv with "[//] [$]") as "H".
    iDestruct "H" as %nodeinv_p.
    unfold nodeinv in nodeinv_p. destruct nodeinv_p as [Hdom [nodeinv_p ]]. by iPureIntro.
  Qed.

  Lemma ghost_update_cssOp_keyset γ_k root p n m Ip In Ip' In' Im' Cp Cn Cp' Cn' Cm' C k res :
      ⊢  ⌜contextualLeq K_multiset (Ip ⋅ In) (Ip' ⋅ In' ⋅ Im')⌝
      ∗ ⌜Cp ## Cn⌝
      ∗ ⌜keyset K Ip p ## keyset K In n⌝
      ∗ ⌜Cp ⊆ keyset K Ip p⌝
      ∗ ⌜Cn ⊆ keyset K In n⌝
      ∗ ⌜keyset K Ip' p ## keyset K In' n⌝
      ∗ ⌜keyset K Ip' p ## keyset K Im' m⌝
      ∗ ⌜keyset K Im' m ## keyset K In' n⌝
      ∗ ⌜keyset K Ip' p ∪ keyset K In' n ∪ keyset K Im' m = keyset K Ip p ∪ keyset K In n⌝
      ∗ ⌜k ∈ keyset K In n⌝
      ∗ ⌜k ∈ KS⌝
      ∗ node root p Ip' Cp'
      ∗ node root n In' Cn'
      ∗ node root m Im' Cm'
      ∗ own γ_k (◯ prod (keyset K In n, Cn) ⋅ ◯ prod (keyset K Ip p, Cp))
      ∗ own γ_k (● prod (KS, C))
      ∗ ⌜Ψ insertOp k (Cp ∪ Cn) (Cp' ∪ Cn' ∪ Cm') res⌝
      ==∗ ∃ C', ⌜Ψ insertOp k C C' res⌝
              ∗ node root p Ip' Cp'
              ∗ node root n In' Cn'
              ∗ node root m Im' Cm'
              ∗ own γ_k (◯ prod (keyset K Ip' p, Cp'))
              ∗ own γ_k (◯ prod (keyset K In' n, Cn'))
              ∗ own γ_k (◯ prod (keyset K Im' m, Cm'))
              ∗ own γ_k (● prod (KS, C'))
              ∗ ⌜domm Ip' = {[p]}⌝
              ∗ ⌜domm In' = {[n]}⌝
              ∗ ⌜domm Im' = {[m]}⌝.
  Proof.
    iIntros "(ContLeq & Disj_pn & Disj_ks_pn & Sub_p & Sub_n & Disj_ks_pn' & Disj_ks_pm'
               & Disj_ks_mn' & ks_eq & k_in_ks & k_in_KS & Hnodep & Hnoden & Hnodem & Hkspn' & HKS & #HΨ)".
    iDestruct "ContLeq" as %ContLeq.
    iDestruct "Disj_pn" as %Disj_pn.
    iDestruct "Disj_ks_pn" as %Disj_ks_pn.
    iDestruct "Sub_p" as %Sub_p.
    iDestruct "Sub_n" as %Sub_n.
    iDestruct "Disj_ks_pn'" as %Disj_ks_pn'.
    iDestruct "Disj_ks_pm'" as %Disj_ks_pm'.
    iDestruct "Disj_ks_mn'" as %Disj_ks_mn'.
    iDestruct "ks_eq" as %ks_eq.
    iDestruct "k_in_ks" as %k_in_ks.
    iDestruct "k_in_KS" as %k_in_KS.
    unfold contextualLeq in ContLeq. destruct ContLeq as [Valid_Ipn [Valid_Ipnm' ContLeq]].
    iPoseProof (extract_from_nodeinv with "[] [$Hnodep]") as "%".
    { iPureIntro. by repeat apply cmra_valid_op_l in Valid_Ipnm'. }
    destruct H0 as [Sub_p' Dom_Ip'].
    iPoseProof (extract_from_nodeinv with "[] [$Hnoden]") as "%".
    { iPureIntro. by apply cmra_valid_op_l, cmra_valid_op_r in Valid_Ipnm'. }
    destruct H0 as [Sub_n' Dom_In'].
    iPoseProof (extract_from_nodeinv with "[] [$Hnodem]") as "%".
    { iPureIntro. by apply cmra_valid_op_r in Valid_Ipnm'. }
    destruct H0 as [Sub_m' Dom_Im'].
    assert (Cp' ## Cn') as Disj_pn'. { clear -Sub_p' Sub_n' Disj_ks_pn'. set_solver. }
    assert (Cn' ## Cm') as Disj_nm'. { clear -Sub_m' Sub_n' Disj_ks_mn'. set_solver. }
    assert (Cm' ## Cp') as Disj_pm'. { clear -Sub_p' Sub_m' Disj_ks_pm'. set_solver. }
    iEval (rewrite -auth_frag_op) in "Hkspn'".
    assert (prod (keyset K Ip' p, Cp') ⋅ prod (keyset K In' n, Cn') ⋅ prod (keyset K Im' m, Cm')
                   = prod (keyset K Ip' p ∪ keyset K In' n ∪ keyset K Im' m, Cp' ∪ Cn' ∪ Cm')).
    { unfold op, prodOp. repeat case_decide; try done. exfalso. try apply H7. set_solver by eauto.
      exfalso. apply H6. clear - Disj_ks_pn' Disj_ks_pm' Disj_ks_mn'. set_solver by eauto.
      exfalso. apply H4. set_solver by eauto. }
    assert (◯ (prod (keyset K Ip' p, Cp') ⋅ prod (keyset K In' n, Cn') ⋅ prod (keyset K Im' m, Cm'))
                   = ◯ (prod (keyset K Ip' p ∪ keyset K In' n ∪ keyset K Im' m, Cp' ∪ Cn' ∪ Cm'))).
    { rewrite H0. reflexivity. }
    assert ((prod (keyset K Ip p, Cp) ⋅ prod (keyset K In n, Cn))
                    = prod (keyset K Ip p ∪ keyset K In n, Cp ∪ Cn)).
    { unfold op, prodOp. repeat case_decide; try done. }
    iMod ((ghost_update_keyset γ_k insertOp k (Cp ∪ Cn) (Cp' ∪ Cn' ∪ Cm') res
                   (keyset K Ip p ∪ keyset K In n) C) with "[HKS Hkspn']") as "Hgks".
    { iEval (rewrite comm) in "Hkspn'". iEval (rewrite H2) in "Hkspn'".
      iFrame "∗ # %". iPureIntro. split.
      rewrite <-ks_eq. clear -Sub_p' Sub_n' Sub_m'. set_solver.
      clear -k_in_ks. set_solver. }
    iDestruct "Hgks" as (C') "(#HΨ' & HKS & H)". iEval (rewrite <-ks_eq) in "H".
    iAssert (own γ_k (◯ (prod (keyset K Ip' p, Cp') ⋅ prod (keyset K In' n, Cn')
                                                    ⋅ prod (keyset K Im' m, Cm'))))
            with "[H]" as "Hv". { iEval (rewrite H1). done. }
    iDestruct "Hv" as "((Hksp' & Hksn') & Hksm')".
    iModIntro. iExists C'. iFrame "∗ # %".
  Qed.

  Lemma ghost_update_cssOp_interface γ_I γ_f root p n m (I Ip In Ip' In' Im': multiset_flowint_ur K) :
      ⊢ ⌜m ∉ domm I⌝
      ∗ ⌜globalinv K root I⌝
      ∗ ⌜contextualLeq K_multiset (Ip ⋅ In) (Ip' ⋅ In' ⋅ Im')⌝
      ∗ own γ_I (● I)
      ∗ own γ_I (◯ (Ip ⋅ In))
      ∗ own γ_f (● domm I)
      ∗ ⌜domm Ip = {[p]}⌝
      ∗ ⌜domm In = {[n]}⌝
      ∗ ⌜domm Ip' = {[p]}⌝
      ∗ ⌜domm In' = {[n]}⌝
      ∗ ⌜domm Im' = {[m]}⌝
      ∗ ⌜inf (Ip' ⋅ In' ⋅ Im') m = 0%CCM⌝
      ==∗ ∃ I', ⌜contextualLeq K_multiset I I'⌝
              ∗ ⌜globalinv K root I'⌝
              ∗ own γ_I (● I')
              ∗ own γ_I (◯ Ip')
              ∗ own γ_I (◯ In')
              ∗ own γ_I (◯ Im')
              ∗ own γ_f (● domm I')
              ∗ ⌜domm I' = domm I ∪ {[m]}⌝
              ∗ ⌜domm I' ∖ {[m]} = domm I⌝.
  Proof.
    iIntros "(m_not_in_I & Hglob & ContLeq & HI & HIpn &
                          Hdomm & Dom_Ip & Dom_In & Dom_Ip' & Dom_In' & Dom_Im' & Hinf)".
    iDestruct "m_not_in_I" as %m_not_in_I.
    iDestruct "Hglob" as %Hglob.
    iDestruct "ContLeq" as %ContLeq.
    iDestruct "Dom_Ip" as %Dom_Ip.
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Dom_Ip'" as %Dom_Ip'.
    iDestruct "Dom_In'" as %Dom_In'.
    iDestruct "Dom_Im'" as %Dom_Im'.
    iDestruct "Hinf" as %m_inf.
    iCombine "HI" "HIpn" as "Hownint".
    iPoseProof (own_valid with "Hownint") as "%". rename H0 into Valid_I_pn.
    apply auth_both_valid_discrete in Valid_I_pn. destruct Valid_I_pn as [Ipn_incl_I Valid_I].
    destruct Ipn_incl_I as [Iz Ipn_incl_I].
    iDestruct "Hownint" as "[HI H']".
    destruct ContLeq as (Valid_Ipn & Valid_Ipnm & Hsub & Hinf_pn & Hout).
    assert (domm (Ip' ⋅ In' ⋅ Im') = domm Ip' ∪ domm In' ∪ domm Im') as Dom_eq.
    { repeat rewrite (flowint_comp_fp); try done. by apply cmra_valid_op_l in Valid_Ipnm. }
    rewrite Dom_Ip' Dom_In' Dom_Im' in Dom_eq.
    assert (m ∉ domm Iz) as m_not_in_Iz.
    { apply leibniz_equiv in Ipn_incl_I.
      rewrite Ipn_incl_I in m_not_in_I.
      rewrite (flowint_comp_fp) in m_not_in_I.
      clear - m_not_in_I. set_solver.
      apply leibniz_equiv_iff in Ipn_incl_I.
      rewrite <-Ipn_incl_I. done. }
    unfold globalinv in Hglob. destruct Hglob as (_ & Hgroot & Hgout & Hgin).
    assert (out Iz m = 0%CCM) as out_Iz_zero.
    {
      apply (intComp_out_zero (Ip⋅In) Iz m). by rewrite <-Ipn_incl_I.
      rewrite <-Ipn_incl_I. done. rewrite <-Ipn_incl_I. apply nzmap_eq.
      intros km. pose proof (Hgout km m) as km_out.
      unfold outset, dom_ms in km_out.
      rewrite (nzmap_elem_of_dom_total) in km_out *; intros km_out.
      apply dec_stable in km_out. rewrite km_out.
      by rewrite nzmap_lookup_empty.
    }
    iMod (own_updateP (flowint_update_P K_multiset I (Ip ⋅ In) (Ip' ⋅ In' ⋅ Im')) γ_I
                            (● I ⋅ ◯ (Ip ⋅ In)) with "[HI H']") as (Io) "H0".
    {
      rewrite Ipn_incl_I.
      apply (flowint_update K_multiset (Iz) (Ip ⋅ In) (Ip' ⋅ In' ⋅ Im')).
      repeat split; try done. apply leibniz_equiv in Ipn_incl_I.
      assert (Valid2_I := Valid_I). rewrite Ipn_incl_I in Valid_I.
      apply intComposable_valid in Valid_I. unfold intComposable in Valid_I.
      destruct Valid_I as (_ & _ & Hdisj & _). rewrite flowint_comp_fp in Hdisj; last first.
      done. rewrite Dom_Ip Dom_In in Hdisj. rewrite Dom_eq.
      clear -Hdisj m_not_in_Iz. set_solver.
      intros nf Hnf. assert (nf = m). rewrite Dom_eq in Hnf.
      rewrite flowint_comp_fp in Hnf; try done. rewrite Dom_Ip Dom_In in Hnf.
      clear -Hnf. set_solver. replace nf.
      unfold out in out_Iz_zero. done.
    }
    { try repeat rewrite own_op; iFrame. }
    iPoseProof ((flowint_update_result γ_I I (Ip ⋅ In) (Ip' ⋅ In' ⋅ Im'))
                        with "H0") as (I'') "(% & % & HIIpnm)".
    rename H0 into ContLeq_I. destruct H1 as [Io' [I_eq I''_eq]].
    assert (Io' = Iz).
    { rewrite Ipn_incl_I in I_eq *; intros I_eq.
      apply intComp_cancelable in I_eq. done.
      by rewrite <-Ipn_incl_I. }
    subst Io'.
    iMod (own_update γ_f (● domm I) (● (domm I ∪ {[m]}) ⋅ ◯ (domm I ∪ {[m]}))
                         with "[Hdomm]") as "H"; try done.
    { apply (auth_update_alloc (domm I) (domm I ∪ {[m]}) (domm I ∪ {[m]})).
      apply gset_local_update. set_solver. }
    assert (domm I'' = domm I ∪ {[m]}) as domm_I''.
    {
      assert (domm I'' = {[p]} ∪ {[n]} ∪ {[m]} ∪ domm Iz) as Dom_I''.
      {
        rewrite I''_eq. repeat rewrite flowint_comp_fp; try congruence; try done.
        by apply cmra_valid_op_l in Valid_Ipnm.
        apply leibniz_equiv_iff in I''_eq.
        rewrite <-I''_eq. unfold contextualLeq in ContLeq_I.
        by destruct ContLeq_I as [_ [? _]].
      }
      assert (domm I = {[p]} ∪ {[n]} ∪ domm Iz) as Dom_I.
      {
        rewrite I_eq. repeat rewrite flowint_comp_fp; try congruence; try done.
        apply leibniz_equiv_iff in I_eq. by rewrite <-I_eq.
      }
      rewrite Dom_I'' Dom_I. clear. set_solver.
    }
    assert (globalinv K root I'').
    {
      apply (contextualLeq_impl_globalinv I I'').
      all : trivial.
      unfold globalinv. repeat split; try done.
      intros n0 Hn0. assert (n0 = m).
      { clear - Hn0 domm_I'' m_not_in_I. set_solver. } subst n0.
      unfold inset. unfold dom_ms. unfold inf. case_eq (inf_map I'' !! m); last first.
      - intros Hm. unfold ccmunit, ccm_unit. simpl. unfold nzmap_dom. simpl. set_solver.
      - intros k0 Hk0. simpl.
        assert (inf (Ip' ⋅ In' ⋅ Im' ⋅ Iz) m = (inf (Ip' ⋅ In'⋅ Im') m) - (out Iz m))%CCM as inf_def.
        { apply intComp_inf_1. apply leibniz_equiv_iff in I''_eq. rewrite <-I''_eq.
          unfold contextualLeq in ContLeq_I. by destruct ContLeq_I as [_ [? _]].
          rewrite Dom_eq. clear. set_solver. }
        rewrite m_inf in inf_def. rewrite out_Iz_zero in inf_def.
        rewrite ccm_pinv_unit in inf_def. unfold inf in inf_def.
        apply leibniz_equiv_iff in I''_eq.
        rewrite <-I''_eq in inf_def. rewrite Hk0 in inf_def.
        simpl in inf_def. rewrite inf_def. unfold ccmunit, lift_unit, nzmap_unit.
        simpl. unfold nzmap_dom. simpl. set_solver.
      }
    iModIntro. iExists I''.
    iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
    iEval (rewrite auth_frag_op) in "HIpnm''". iDestruct "HIpnm''" as "(HIpn' & HIm')".
    iEval (rewrite auth_frag_op) in "HIpn'". iDestruct "HIpn'" as "(HIp' & HIn')".
    iDestruct "H" as "(Hdomm & _)". iEval (rewrite <-domm_I'') in "Hdomm".
    iFrame "∗ # %". iPureIntro. clear - domm_I'' m_not_in_I. set_solver.
  Qed.
  
  (** High-level lock specs **)

  Lemma lockNode_spec_high γ_I γ_f γ_k γ_c root n :
    ⊢ inFP γ_f n -∗ css_inv γ_I γ_f γ_k γ_c root
      -∗ <<< True >>>
           lockNode #n @ ⊤ ∖ ↑N
         <<< ∃ In Cn, nodePred γ_I γ_k root n In Cn,
             RET #() >>>.
  Proof.
    iIntros "#HFp #HInv".
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "HInv" as ">Hcss". iDestruct "Hcss" as (I C) "Hcssi".
    iPoseProof (inFP_domm with "[$] [$]") as "%". rename H0 into n_in_I.
    iPoseProof (CSS_unfold with "[$] [%]") as "(Hg & Hnf & Hcss')"; try done.
    iSpecialize ("Hcss'" $! C).
    iDestruct "Hnf" as (b In Cn) "Hlock". iFrame.
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iPoseProof ("Hcss'" with "[-AU]") as "Hcss".
      { iFrame. iExists b, In, Cn. iFrame. }
      iSplitL "Hcss"; try done. iNext. iExists I, C. iFrame.
    }
    iIntros "(Hlockn & H)". 
    iMod "AU" as "[_ [_ Hclose]]".
    iDestruct "Hlockn" as "(Hlockn & _)".
    iMod ("Hclose" with "[H]") as "HΦ"; try done. iModIntro.
    iPoseProof ("Hcss'" with "[-HΦ]") as "Hcss".
    { iFrame. iExists true, In, Cn. iFrame. }
    iFrame. iNext. iExists I, C. eauto with iFrame.
  Qed.

  Lemma unlockNode_spec_high γ_I γ_f γ_k γ_c root (n: Node) In Cn :
    ⊢ css_inv γ_I γ_f γ_k γ_c root ∗ nodePred γ_I γ_k root n In Cn
      -∗  <<< True  >>>
           unlockNode #n @ ⊤ ∖ ↑N
          <<< True, RET #() >>>.
  Proof.
    iIntros "(#HInv & Hnp)". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "HInv" as ">Hcss". iDestruct "Hcss" as (I C) "Hcssi".
    iDestruct "Hnp" as "(node & Hnpks & HnpI & Dom_In)".
    iPoseProof (int_domm with "[$] [$] [$]") as "%". rename H0 into n_in_I.
    iPoseProof (CSS_unfold_node_wand with "[$] [$] [%]")
      as "(Hn & Hg & Hlock & Hcss')"; try done.
    iAssert (nodePred γ_I γ_k root n In Cn)%I 
      with "[Hnpks HnpI Dom_In Hn]" as "Hnp".
    { iFrame. }
    iCombine "Hlock" "Hnp" as "HPre".      
    iAaccIntro with "HPre".
    { iIntros "(Hlock & Hnp)". iModIntro. iFrame. iNext. 
      iExists I, C. iApply "Hcss'". iFrame. iExists true, In, Cn. iFrame. }
    iIntros "Hlock".
    iMod "AU" as "[_ [_ Hclose]]".
    iMod ("Hclose" with "[]") as "HΦ"; try done.
    iModIntro. iFrame. iNext. iExists I, C.
    iApply "Hcss'". iFrame. iExists false, In, Cn. iFrame.
  Qed.

  (** Proof of the lock-coupling template *)

  Theorem create_spec :
   ⊢ {{{ True }}}
        create #()
     {{{ γ_I γ_f γ_k γ_c (root: Node), RET #root; 
          css_inv γ_I γ_f γ_k γ_c root ∗ css_cont γ_c ∅ }}}.
  Proof.
    iIntros (Φ). iModIntro.
    iIntros "_ HΦ".
    wp_lam. wp_apply allocRoot_spec; try done.
    iIntros (root Ir ks) "(node & Hl & HIr & Hks)".
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
    iMod (own_alloc (● (Some (Excl ∅)) ⋅ ◯ (Some (Excl ∅)))) 
      as (γ_c)"(Hc● & Hc◯)".
    { apply auth_both_valid_discrete. split; try done. }
    iModIntro. wp_pures.
    iMod (inv_alloc N _ (CSS γ_I γ_f γ_k γ_c root) with "[-HΦ Hc◯]") as "#css_inv".
    { iNext. iExists Ir, ∅. iFrame. iSplitR.
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
      - assert (domm Ir = {[root]}) as Domm_Ir.
        { subst Ir; unfold domm, dom, flowint_dom, inf_map; simpl.
          apply leibniz_equiv. by rewrite dom_singleton. }
        rewrite Domm_Ir. rewrite big_opS_singleton.
        iExists false, Ir, ∅. iFrame "∗%".
        assert (keyset K Ir root = KS) as Hkeyset.
        { unfold keyset. unfold dom_ms, inf, out; subst Ir; simpl.
          rewrite nzmap_lookup_empty. rewrite lookup_singleton.
          unfold ccmunit at 2. unfold ccm_unit. simpl.
          unfold nzmap_dom. simpl.
          assert (dom (gset K) (∅: gmap K nat) = ∅) as H'.
          { apply leibniz_equiv. by rewrite dom_empty. }
          rewrite H' Hks. set_solver. }
        by rewrite Hkeyset. }
      iModIntro. 
      iApply ("HΦ" $! γ_I γ_f γ_k γ_c root); try iFrame "∗#".    
  Qed.    

  Lemma traverse_spec γ_I γ_f γ_k γ_c root k p n Ip Cp In Cn:
    ⊢ ⌜k ∈ KS⌝ ∗ css_inv γ_I γ_f γ_k γ_c root -∗
    {{{   inFP γ_f n ∗ inFP γ_f p ∗ inFP γ_f root ∗ ⌜n ≠ root⌝
        ∗ nodePred γ_I γ_k root n In Cn ∗ nodePred γ_I γ_k root p Ip Cp
        ∗ ⌜in_inset K k Ip p⌝ ∗ ⌜in_outset K k Ip n⌝
    }}}
      traverse #p #n #k @ ⊤
    {{{ p' n' Ip' In' Cp' Cn' (res: bool), RET ((#p', #n'), #res);
          inFP γ_f n' ∗ inFP γ_f p'
        ∗ nodePred γ_I γ_k root n' In' Cn' ∗ nodePred γ_I γ_k root p' Ip' Cp'
        ∗ ⌜in_inset K k Ip' p'⌝
        ∗ ⌜in_outset K k Ip' n'⌝
        ∗ ⌜¬in_outsets K k In'⌝
        ∗ ⌜res ↔ k ∈ Cn'⌝
    }}}.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "!# H HCont".
    iLöb as "IH" forall (p n Ip In Cp Cn).
    iDestruct "H" as "(#Hfpn & #Hfpp & #Hfpr & % & Hnp_n & Hnp_p & % & %)".
    rename H0 into k_in_KS. rename H1 into n_neq_root.
    rename H2 into in_inset_Ip. rename H3 into in_outset_Ip.
    wp_lam. wp_pures. wp_bind (findNext _ _)%E.
    (* Preparing pre-condition of findNext *)
    iDestruct "Hnp_n" as "(noden & Hkn & Hin & Dom_In)".
    iDestruct "Hnp_p" as "(nodep & Hkp & Hip & Dom_Ip)".
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Dom_Ip" as %Dom_Ip.
    iCombine "Hip" "Hin" as "H".
    iPoseProof (own_valid with "[$]") as "%". rename H0 into Valid_Inp.
    assert (in_inset K k In n) as in_inset_In.
    { apply (flowint_inset_step Ip In k n); try done. apply auth_frag_valid. done. set_solver. }
    wp_apply ((findNext_spec n k In Cn root) with "[noden]").
    { iFrame "∗ %". } iDestruct "H" as "(Hip & Hin)".
    iIntros (b n' res) "(noden & % & Hb)". rename H0 into Hres. destruct b.
    - (* findNext returns Some n' *)
      iDestruct "Hb" as %in_outset_In. wp_pures.
      wp_bind (lockNode _)%E. iApply fupd_wp.
      (* Open invariant to get pre for lockNode_spec *)
      iInv "HInv" as ">Hcss".
      iAssert (nodePred γ_I γ_k root n In Cn)%I with "[noden Hkn Hin]"
                        as "Hnp_n". { iFrame "∗ %". }
      (* ghost update to step to n' *)
      iMod (ghost_update_step with "[$] [$] [% //] [% //]") as "(Hcss & Hnp_n & #Hfpn')".
      iModIntro. iSplitL "Hcss". by iNext. iModIntro.
      (* Lock node n' *)
      awp_apply (lockNode_spec_high) without "HCont".
      iFrame "Hfpn'". iFrame "HInv".
      iAaccIntro with "[]"; first done. { eauto with iFrame. }
      (* Receive post of lock_spec_high *)
      iIntros (In' Cn') "Hnp_n'".
      iModIntro. iIntros "HCont". wp_pures.
      iAssert (nodePred γ_I γ_k root p Ip Cp)%I with "[nodep Hkp Hip]"
                        as "Hnp_p". { iFrame "∗ %". }
      (* Unlock node p *)
      awp_apply (unlockNode_spec_high with "[Hnp_p]") without "HCont".
      { iFrame "Hnp_p HInv". }
      iAaccIntro with "[]"; first done. { eauto with iFrame. }
      iIntros "_"; iModIntro. iIntros "HCont". wp_pures.
      (* Open invariant and prepare pre for induction hypothesis *)
      iApply fupd_wp. iInv "HInv" as ">Hcss".
      iDestruct "Hcss" as (I C) "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
      iDestruct "Hnp_n" as "(noden & Hkn & Hin & Dom_In)".
      iDestruct "Hnp_n'" as "(noden' & Hkn' & Hin' & Dom_In')".
      iDestruct "Hglob" as %Hglob.
      iDestruct "Dom_In'" as %Dom_In'.
      iPoseProof ((own_op γ_I (◯ In) (◯ In')) with "[Hin Hin']") as "H";
                     first by eauto with iFrame.
      iEval (rewrite -auth_frag_op) in "H".
      iPoseProof ((auth_own_incl _ I) with "[$HI $H]") as (Io)"%".
      rename H0 into I_incl.
      iPoseProof (own_valid with "H") as "%". rename H0 into Valid_Inn'.
      iPoseProof (node_implies_nodeinv with "[] [$noden']") as "%".
      { iPureIntro. rewrite auth_frag_valid in Valid_Inn' *; intros Valid_Inn'.
        by apply cmra_valid_op_r in Valid_Inn'. } rename H0 into nodeinv_n'.
      assert (n' ≠ root) as n'_neq_root.
      { apply (successor_not_root I In In' Io Cn' root n' k); try done. }
      (* Close invariant *)
      iModIntro. iSplitL "HI Hks Hcont Hbigstar Hdom".
      iNext. iExists I, C. iFrame "∗ # %". iModIntro.
      iDestruct "H" as "(Hin & Hin')".
      iAssert (nodePred γ_I γ_k root n In Cn)%I with "[noden Hkn Hin]"
                        as "Hnp_n". { iFrame "∗ %". }
      iAssert (nodePred γ_I γ_k root n' In' Cn')%I with "[noden' Hkn' Hin']"
                        as "Hnp_n'". { iFrame "∗ %". }
      (* Apply induction hypothesis *)
      iSpecialize ("IH" $! n n' In In' Cn Cn').
      iApply ("IH" with "[Hnp_n Hnp_n']"). iFrame "∗ # %".
      iNext. done.
    - (* findNext returns None *)
      wp_pures. wp_bind (findNext _ _)%E.
      wp_apply (findNext_spec with "[noden]"). iFrame "∗ %".
      iIntros (suc n0 res0)"(Hnoden & Hres & Hsuc)". iDestruct "Hb" as "(% & %)".
      iDestruct "Hres" as "%".
      (* Apply continuation *)
      iSpecialize ("HCont" $! p n Ip In Cp Cn).
      destruct suc; wp_pures; iApply "HCont"; 
      iFrame "∗ # %"; iModIntro; try done.
  Qed.

  

  (* TODO uses old version of node_lock_not_in_FP *)
  Theorem searchStrOp_spec γ_I γ_f γ_k γ_c root (k: K) :
    ⊢ ⌜k ∈ KS⌝ ∗ css_inv γ_I γ_f γ_k γ_c root -∗
    <<< ∀ (C: gset K), css_cont γ_c C >>>
      CSS_insertOp root #k @ ⊤ ∖ ↑N
    <<< ∃ (C' : gset K) (res: bool), css_cont γ_c C'
                        ∗ ⌜Ψ insertOp k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "(k_in_KS & #HInv)". iIntros (Φ) "AU".
    iDestruct "k_in_KS" as %k_in_KS.
    wp_lam. wp_bind (lockNode _)%E.
    iApply fupd_wp. iInv "HInv" as ">Hcss".
    iMod (ghost_update_root with "[$]") as "(Hcss & #HinFPr)".
    iModIntro. iSplitR "AU". by iNext. iModIntro.
    (* Lock root *)
    awp_apply (lockNode_spec_high γ_I γ_f γ_k γ_c root root); try done.
    iAaccIntro with "[]"; try eauto with iFrame.
    iIntros (Ir Cr) "Hnp". iModIntro. wp_pures.
    wp_bind (findNext _ _)%E.
    (* Preparing pre-condition of findNext *)
    iApply fupd_wp. iInv "HInv" as ">Hcss".
    iDestruct "Hcss" as (I1 C1) "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
    iDestruct "Hglob" as %Hglob1.
    iDestruct "Hnp" as "(Hnode & Hk & Hi & Dom_In)".
    iDestruct "Dom_In" as %Dom_In.
    iPoseProof ((auth_own_incl _ I1) with "[$HI $Hi]") as (Io')"%".
    rename H0 into Ir_incl_I1.
    iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I1.
    assert (in_inset K k Ir root) as k_inset_root.
    { unfold globalinv in Hglob1. destruct Hglob1 as [_ [_ [_ Hglob1_inset]]].
      pose proof (Hglob1_inset k k_in_KS).
      apply (inset_monotone I1 Ir Io' k root); try done.
      by apply auth_auth_valid. set_solver. }
    iModIntro. iSplitL "Hbigstar Hcont Hdom Hks HI".
    iNext. iExists I1, C1. iFrame "∗ %". iModIntro.
    wp_apply ((findNext_spec root k Ir Cr root) with "[Hnode]").
    { iFrame "∗ %". } iIntros (b n res0) "(Hnode & Hres & Hb)".
    iDestruct "Hres" as %Hres.
    destruct b; last first.
    { (* (findNext root) returns None; contradiction *)
      iDestruct "Hb" as "(_ & root_neq)".
      iDestruct "root_neq" as %root_neq.
      contradiction. }
    (* (findNext root) return Some n *)
    iDestruct "Hb" as %in_outset_r.
    wp_pures. wp_bind (lockNode _)%E.
    (* Open invariant to show n in the footprint *)
    iApply fupd_wp. iInv "HInv" as ">Hcss".
    iDestruct "Hcss" as (I2 C2) "Hcssi".
    iDestruct "Hcssi" as "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
    iDestruct "Hglob" as %Hglob2.
    iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I2.
    iPoseProof ((auth_own_incl _ I2) with "[$HI $Hi]") as (Io'')"%".
    rename H0 into Ir_incl_I2.
    assert (n ∈ domm I2) as n_in_I2.
    { assert (n ∈ domm Io'').
      { apply (flowint_step I2 Ir Io'' k n); try done.
        rewrite auth_auth_valid in Valid_I2*. done.
        unfold globalinv in Hglob2.
        destruct Hglob2 as (_ & _ & cI & _). done.
      }
      rewrite Ir_incl_I2. rewrite flowint_comp_fp. set_solver.
      rewrite <-Ir_incl_I2. by apply auth_auth_valid. }
    iMod (ghost_snapshot_fp γ_f (domm I2) n with "[$Hdom] [% //]")
        as "(Hdom & #Hinfpn)".
    iModIntro. iSplitL "HI Hks Hcont Hbigstar Hdom".
    iNext. iExists I2, C2. iFrame "∗ %". iModIntro.
    (* Lock n *)
    awp_apply (lockNode_spec_high γ_I γ_f γ_k γ_c root n); try done.
    iAaccIntro with "[]"; try eauto with iFrame.
    iIntros (In Cn) "Hnpn".
    iModIntro. wp_pures. wp_bind (traverse _ _ _)%E.
    (* Open invariant for pre of traverse *)
    iApply fupd_wp. iInv "HInv" as ">Hcss".
    iDestruct "Hcss" as (I3 C3) "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
    iDestruct "Hglob" as %Hglob3.
    iDestruct "Hnpn" as "(Hnoden & Hkn & Hin & Dom_Inn)".
    iPoseProof ((own_op γ_I (◯ Ir) (◯ In)) with "[Hi Hin]") as "H";
                     first by eauto with iFrame.
    iEval (rewrite -auth_frag_op) in "H".
    clear Io' Ir_incl_I1 Io'' Ir_incl_I2.
    iPoseProof ((auth_own_incl _ I3) with "[$HI $H]") as (Io)"%".
    rename H0 into Irn_incl_I3.
    iPoseProof (own_valid with "H") as "%". rename H0 into Valid_Irn.
    iPoseProof (node_implies_nodeinv with "[] [$Hnoden]") as "%".
    { iPureIntro. rewrite auth_frag_valid in Valid_Irn *; intros Valid_Irn.
      by apply cmra_valid_op_r in Valid_Irn. } rename H0 into nodeinv_n.
    assert (n ≠ root) as n_neq_root.
    { apply (successor_not_root I3 Ir In Io Cn root n k); try done. }
    (* Close invariant *)
    iModIntro. iSplitL "HI Hks Hcont Hbigstar Hdom".
    iNext. iExists I3, C3. iFrame "∗ # %". iModIntro.
    iDestruct "H" as "(Hi & Hin)".
    iDestruct "Dom_Inn" as %Dom_Inn.
    (* Apply traverse_spec *)
    wp_apply ((traverse_spec γ_I γ_f γ_k γ_c root k root n Ir Cr In Cn)
                 with "[] [-AU]"); try iFrame "∗ % #".
    iIntros (p' n' Ip' In' Cp' Cn' res) "(#HinFPn' & # HinFPp'
                            & Hnpn' & Hnpp' & H1 & H2 & H3 & H4)".
    iDestruct "H1" as %inset_p'. iDestruct "H2" as %outset_pn'.
    iDestruct "H3" as %not_outset_n'. clear Hres. iDestruct "H4" as %Hres.
    wp_pures. destruct res.
    - (* The traverse spec returns the operation key is already present.
         In this case, we do not need to add a new node.
         So, we open AU and show post-condition *)
      iInv "HInv" as ">Hcss".
      iDestruct "Hcss" as (I4 C4) "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
      iDestruct "Hnpn'" as "(Hnoden & Hkn & Hin & Dom_Inn)".
      iPoseProof (Ψ_key_present with "[% //] [$Hks] [$Hkn]") as "(Hks & Hkn & #HΨ)".
      (* Open AU *)
      iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
      iDestruct (auth_agree with "Hcont Hc") as %<-.
      wp_pures. iSpecialize ("Hclose" $! C4 false).
      (* Close AU *)
      iMod ("Hclose" with "[Hc]") as "HΦ". iFrame "∗ #".
      iModIntro. iModIntro. iSplitR "HΦ". iNext.
      iExists I4, C4. iFrame "∗ %". done.
    - (* The traverse spec returns the operation key is not present.
         Here, we create a new node m *)
      wp_pures.
      (* alloc m *)
      wp_apply (alloc_spec); first done.
      iIntros (m lm) "(Hrepm & % & Hlm)". wp_pures. wp_bind (decisiveOp _ _ _ _)%E.
      rename H0 into Lock_m. iEval (rewrite <-Lock_m) in "Hlm".
      (* Open invariant for pre of decisiveOp *)
      iApply fupd_wp. iInv "HInv" as ">Hcss". iDestruct "Hcss" as (I4 C4) "Hcss".
      iPoseProof (node_lock_not_in_FP with "[$] [$]") as "%". rename H0 into m_not_in_I4.
      iPoseProof (inFP_domm with "[$HinFPr] [$]") as "%". rename H0 into n_in_I.
      assert (m ≠ root) as m_neq_root. { set_solver. }
      iDestruct "Hnpn'" as "(Hnoden & Hkn & Hin & Dom_Inn)". iDestruct "Dom_Inn" as %Dom_In'.
      iDestruct "Hnpp'" as "(Hnodep & Hkp & Hip & Dom_Inp)". iDestruct "Dom_Inp" as %Dom_Ip'.
      iPoseProof ((own_op γ_I (◯ Ip') (◯ In')) with "[Hip Hin]") as "HIpn'"; first by eauto with iFrame.
      iPoseProof (own_valid with "HIpn'") as "%". rename H0 into Valid_Ipn'.
      rewrite -auth_frag_op in Valid_Ipn'. rewrite auth_frag_valid in Valid_Ipn' *; intros Valid_Ipn'.
      iPoseProof ((own_op γ_k _ _) with "[Hkp Hkn]") as "Hkspn'"; first by eauto with iFrame.
      iPoseProof (own_valid with "Hkspn'") as "%". rename H0 into Valid_kspn'.
      rewrite -auth_frag_op in Valid_kspn'. rewrite auth_frag_valid in Valid_kspn' *; intros Valid_kspn'.
      unfold op, cmra_op in Valid_kspn'. simpl in Valid_kspn'.
      unfold ucmra_op in Valid_kspn'. simpl in Valid_kspn'. repeat case_decide; try done .
      rename H0 into c_sub_ks_n. rename H1 into c_sub_ks_p.
      rename H2 into Disj_ks_pn. rename H3 into Disj_c_pn.
      iEval (rewrite -auth_frag_op) in "HIpn'".
      iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
      iDestruct "Hglob" as %Hglob4.
      iPoseProof ((auth_own_incl _ I4) with "[$HI $HIpn']") as (Iw)"%".
      rename H0 into Ipn_incl_I4.
      iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I4.
      iPoseProof (own_valid with "HIpn'") as "%". rename H0 into Valid_Ipn.
      assert (out (Ip'⋅In') m = 0%CCM) as Out_zero_pn'.
      {
        apply (intComp_out_zero Iw (Ip'⋅In') m).
        rewrite intComp_comm. rewrite <-Ipn_incl_I4.
        by apply auth_auth_valid.
        rewrite intComp_comm. by rewrite <-Ipn_incl_I4.
        rewrite intComp_comm. rewrite <-Ipn_incl_I4.
        unfold globalinv in Hglob4. destruct Hglob4 as (_ & _ & Hglob4 & _).
        apply nzmap_eq. intros k0. pose proof (Hglob4 k0 m) as k_not_out.
        unfold outset, dom_ms in k_not_out.
        rewrite (nzmap_elem_of_dom_total) in k_not_out *; intros k_not_out.
        apply dec_stable in k_not_out. by rewrite nzmap_lookup_empty.
      }
      clear n_neq_root nodeinv_n.
      iPoseProof (node_implies_nodeinv with "[] [$Hnoden]") as "%".
      { iPureIntro. rewrite auth_frag_valid in Valid_Ipn *; intros Valid_Ipn.
        by apply cmra_valid_op_r in Valid_Ipn. } rename H0 into nodeinv_n.
      assert (n' ≠ root) as n_neq_root.
      { apply (successor_not_root I4 Ip' In' Iw Cn' root n' k); try done. }
      (* Close invariant *)
      iModIntro. iSplitL "HI Hks Hcont Hbigstar Hdom". iNext.
      iExists I4, C4. iFrame "∗ # %". iModIntro.
      destruct Hres as [Hres Hk_not0].
      assert (k ∉ Cn') as Hk_not1. { unfold not. apply Hk_not0. }
      (* Apply decisiveOp_spec *)
      wp_apply ((decisiveOp_insert_spec root p' n' m k Ip' In' Cp' Cn')
            with "[Hnodep Hnoden Hrepm]"). { iFrame "∗ % #". iPureIntro. set_solver. }
      iIntros (Cp'' Cn'' Cm'' Ip'' In'' Im'' res) "(Hnodep' & Hnoden' & Hnodem' & #HΨ & HcontLeq & Hminf & H)".
      iDestruct "H" as "(Disj_ks_pn & Disj_ks_pm & Disj_ks_mn & ks_eq)".
      iDestruct "Hminf" as %Hinf.
      iDestruct "HcontLeq" as %HcontLeq.
      iDestruct "Disj_ks_pn" as %Disj_ks_pn'.
      iDestruct "Disj_ks_pm" as %Disj_ks_pm'.
      iDestruct "Disj_ks_mn" as %Disj_ks_mn'.
      iDestruct "ks_eq" as %ks_eq.

      (* Linearization starts *)
      iApply fupd_wp. iInv "HInv" as ">Hcss".
      iDestruct "Hcss" as (I5 C5) "((HI & Hglob & Hks & Hdom & Hcont) & Hbigstar)".
      (* Open AU *)
      iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
      iDestruct (auth_agree with "Hcont Hc") as %<-.

      (* ------ update keyset ghost resources -------*)

      assert (in_inset K k In' n') as in_inset_n.
      { apply (flowint_inset_step Ip' In' k n'); try done.
        rewrite Dom_In'. clear. set_solver. }
      assert (k ∈ keyset K In' n') as in_keyset_n.
      { apply keyset_def; try done. }
      iMod (ghost_update_cssOp_keyset with "[Hnodep' Hnoden' Hnodem' Hks Hkspn']") as "Hgks".
      { iFrame "HΨ". iFrame "∗". iFrame "%".
        iPureIntro. split; try set_solver. }
      iDestruct "Hgks" as (C5') "(#HΨ' & Hnodep' & Hnoden' & Hnodem' & Hksp'
                                       & Hksn' & Hksm' & HKS & % & % & %)".
      rename H0 into Dom_Ip''.
      rename H1 into Dom_In''.
      rename H2 into Dom_Im''.
      iMod (auth_excl_update γ_c (C5') with "Hcont Hc") as "[Hcont Hc]".

      (* ------ update interface ghost resources -------*)

      iPoseProof (node_lock_not_in_FP with "[$Hlm] [$]") as "%". rename H0 into m_not_in_I5.
      iDestruct "Hglob" as %Hglob5.
      iMod (ghost_update_cssOp_interface with "[HIpn' HI Hdom]") as "Hgi".
      { iFrame "∗". iPureIntro. split. apply m_not_in_I5.
        split; try apply Hglob5. split; try apply HcontLeq.
        repeat split; try done. }
      iDestruct "Hgi" as (I') "(ContLeq_I & Hglob_I' & HI & HIp' & HIn'
                                & HIm' & Hdomm & Dom_I' & Dom2_I')".
      iDestruct "ContLeq_I" as %ContLeq_I.
      iDestruct "Hglob_I'" as %Hglob_I'.
      iDestruct "Dom_I'" as %Dom_I'.
      iDestruct "Dom2_I'" as %Dom2_I'.

      (* ------ updates over, close AU -------*)

      iSpecialize ("Hclose" $! C5' res).
      iMod ("Hclose" with "[Hc]") as "HΦ". iFrame "∗ % #".
      iModIntro. iSplitL "Hbigstar HKS Hcont HI Hdomm Hnodem' Hksm' HIm' Hlm".
      iNext. iExists I', C5'. iFrame "∗ # %".
      { rewrite (big_sepS_delete _ (domm I') m); last first.
      clear -Dom_I'. set_solver. iEval (rewrite Dom2_I').
      iFrame. iExists false. iFrame "∗ %". iExists Im'', Cm''. iFrame "∗ %". }
      iModIntro. wp_pures. wp_bind (unlockNode _)%E.

      (* ------ linearization over -------*)

      iAssert (nodePred γ_I γ_k root p' Ip'' Cp'')%I with "[Hnodep' Hksp' HIp']"
                        as "Hnp_p". { iFrame "∗ %". }
      (* Unlock node p *)
      awp_apply (unlockNode_spec_high with "[Hnp_p]") without "HΦ".
      iFrame "Hnp_p HInv".
      iAaccIntro with "[]"; first done.
      { iIntros "_". iModIntro.
        iFrame "∗ %". }
      iIntros "_". iModIntro. iIntros "HΦ". wp_pures.
      iAssert (nodePred γ_I γ_k root n' In'' Cn'')%I with "[Hnoden' Hksn' HIn']"
                        as "Hnp_n". { iFrame "∗ %". }
      (* Unlock node n *)
      awp_apply (unlockNode_spec_high with "[Hnp_n]") without "HΦ".
      iFrame "Hnp_n HInv".
      iAaccIntro with "[]"; first done.
      { eauto with iFrame. }
      iIntros "_". iModIntro. iIntros "HΦ". wp_pures. done.
  Qed.

End Coupling_Template.

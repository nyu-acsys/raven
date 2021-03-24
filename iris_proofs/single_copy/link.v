(** Verification of Give-up template algorithm *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset frac.
From iris.algebra.lib Require Import frac_agree.
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
Section Link_Cameras.

  (* RA for authoritative flow interfaces over pairs of multisets of keys *)
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

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.
  
  (* RA for authoritative inreach sets *)
  Class inreachG Σ := InreachG { inreach_inG :> inG Σ (authR (gsetUR K)) }.
  Definition inreachΣ : gFunctors := #[GFunctor (authR (gsetUR K))].

  Instance subG_inreachΣ {Σ} : subG inreachΣ Σ → inreachG Σ.
  Proof. solve_inG. Qed.

  (* RA for fractional interfaces *)
  Class fracintG Σ :=
    FracinthG { fracint_inG :> inG Σ (frac_agreeR (multiset_flowint_ur K)) }.
  Definition fracintΣ : gFunctors := #[GFunctor (frac_agreeR (multiset_flowint_ur K))].

  Instance subG_fracintΣ {Σ} : subG fracintΣ Σ → fracintG Σ.
  Proof. solve_inG. Qed.

  (* RA for ghost locations *)
  Class ghost_heapG Σ :=
    Ghost_heapG { ghost_heap_inG :> inG Σ (authR $ gmapUR Node $ agreeR $ prodO gnameO gnameO) }.
  Definition ghost_heapΣ : gFunctors := #[GFunctor (authR $ gmapUR Node $ agreeR $ prodO gnameO gnameO)].

  Instance subG_ghost_heapΣ {Σ} : subG ghost_heapΣ Σ → ghost_heapG Σ.
  Proof. solve_inG. Qed.


End Link_Cameras.

(** Verification of the template *)
Section Link_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ, !inreachG Σ,
    !fracintG Σ, !ghost_heapG Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the link template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b-link-core.spl and
   * hashtbl-link.spl for the concrete implementations. *)

  (* TODO add alias inreach = inset for this file. *)

  Parameter allocRoot : val.
  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).

  Definition create : val :=
    λ: <>,
      let: "r" := allocRoot #() in
      "r".

  Definition traverse : val :=
    rec: "tr" "n" "k" :=
      lockNode "n";;
      match: (findNext "n" "k") with
        NONE => "n"
      | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
      end.

  Definition CSSOp (Ψ: dOp) (r: Node) : val :=
    rec: "dictOp" "k" :=
      let: "n" := traverse #r "k" in
      match: ((decisiveOp Ψ) "n" "k") with
        NONE => unlockNode "n";; "dictOp" "k"
      | SOME "res" => unlockNode "n";; "res"
      end.

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     b-link.spl and hashtbl-link.spl for the concrete definitions. *)
  Parameter node : Node → multiset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Hypothesis node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-link.spl and b-link.spl *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C',
    node n I_n C ∗ node n I_n' C' -∗ False.


  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper
   * (see b-link.spl and hashtbl-link.spl *)

  Parameter allocRoot_spec :
      ⊢ ({{{ True }}}
           allocRoot #()
         {{{ (r: Node) (Ir: multiset_flowint_ur K) (ks: nzmap K nat),
             RET #r; node r Ir ∅ ∗ (lockLoc r) ↦ #false 
                     ∗ ⌜Ir = int {| infR := {[r := ks]}; outR := ∅ |}⌝
                     ∗ ⌜dom (gset K) ks = KS⌝
                     }}})%I.

  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : multiset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ }}}
         findNext #n #k
       {{{ (succ: bool) (np: Node),
           RET (match succ with true => (SOMEV #np) | false => NONEV end);
           node n In C ∗ (match succ with
                            true => ⌜in_outset K k In np⌝
                          | false => ⌜¬in_outsets K k In⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (In: multiset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ ∗ ⌜¬in_outsets K k In⌝ }}}
         decisiveOp dop #n #k
       {{{ (succ: bool) (res: bool) (C1: gset K),
           RET (match succ with false => NONEV | true => (SOMEV #res) end);
           node n In C1 ∗ (match succ with false => ⌜C = C1⌝
                                         | true => ⌜Ψ dop k C C1 res⌝
                           end) }}})%I.

  (** The concurrent search structure invariant *)

  Definition inFP γ_f n : iProp :=
    ∃ (N: gset Node), own γ_f (◯ N) ∗ ⌜n ∈ N⌝.

  Definition inInr γ_in k : iProp :=
    ∃ (Ks: gset K), own (γ_in) (◯ Ks) ∗ ⌜k ∈ Ks⌝.

  Definition nodePred γ_f γ_gh γ_k n In Cn : iProp :=
    ∃ γ_hn γ_in, 
      node n In Cn
    ∗ own (γ_hn) ((to_frac_agree (1/2) In))
    ∗ own γ_k (◯ prod (keyset K In n, Cn))
    ∗ inFP γ_f n
    ∗ own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}).

  Definition nodeShared γ_I γ_gh n In : iProp :=
    ∃ γ_hn γ_in,  
      own γ_I (◯ In)
    ∗ own (γ_hn) ((to_frac_agree (1/2) In))
    ∗ ⌜domm In = {[n]}⌝    (* Needed for globalinv_root_ins *)
    ∗ own (γ_in) (● (inset K In n))
    ∗ own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}).

  Definition nodeFull γ_I γ_f γ_k γ_gh n : iProp :=
    (∃ (b: bool) In Cn,
        lockR b n (nodePred γ_f γ_gh γ_k n In Cn)
        ∗ nodeShared γ_I γ_gh n In).
  
  Definition globalGhost γ_I γ_k γ_f γ_gh hγ r I C : iProp :=
    (own γ_I (● I) ∗ ⌜globalinv K r I⌝ ∗ own γ_k (● prod (KS, C))
     ∗ own γ_f (● domm I) ∗ own γ_gh (● hγ)).

  Definition CSSi γ_I γ_f γ_k γ_gh hγ r C I : iProp :=
    (globalGhost γ_I γ_k γ_f γ_gh hγ r I C
     ∗ ([∗ set] n ∈ (domm I), nodeFull γ_I γ_f γ_k γ_gh n)
    )%I.

  Definition CSS γ_I γ_f γ_k γ_gh r C : iProp :=
    (∃ hγ I, CSSi γ_I γ_f γ_k γ_gh hγ r C I)%I.

  (** Some useful lemmas *)

  Lemma inFP_domm γ_I γ_f γ_k γ_gh hγ r C I n :
    inFP γ_f n -∗ CSSi γ_I γ_f γ_k γ_gh hγ r C I -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom & Hgh) & Hbigstar)".
    iDestruct "Hfp" as (N) "(#Hdom' & n_in_N)". iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N) with "[$]") as "#N_incl".
    iDestruct "N_incl" as %N_incl.
    apply gset_included in N_incl.
    iPureIntro. set_solver.
  Qed.
  
  Lemma frac_int_equal γ_hn In In' :
    own γ_hn (to_frac_agree (1/2) In) -∗ own γ_hn (to_frac_agree (1/2) In') -∗ ⌜In = In'⌝.
  Proof.
    iIntros.
    iPoseProof ((own_valid_2 (γ_hn) (to_frac_agree (1/2) In) (to_frac_agree (1/2) In'))
                  with "[$] [$]") as "%"; try done.
    iPureIntro.
    apply frac_agree_op_valid in H0.
    destruct H0 as [_ H0].
    by apply leibniz_equiv.
  Qed.
    
  Lemma CSS_unfold γ_I γ_f γ_k γ_gh r C n :
    CSS γ_I γ_f γ_k γ_gh r C -∗ inFP γ_f n
    -∗ (∃ hγ I, globalGhost γ_I γ_k γ_f γ_gh hγ r I C 
        ∗ nodeFull γ_I γ_f γ_k γ_gh n
        ∗ (∀ C',
           globalGhost γ_I γ_k γ_f γ_gh hγ r I C' ∗ nodeFull γ_I γ_f γ_k γ_gh n
           -∗ CSS γ_I γ_f γ_k γ_gh r C')).
  Proof.
    iIntros "Hcss #Hfp".
    iDestruct "Hcss" as (hγ I) "((HI & Hglob & Hks & Hdom & Hgh) & Hbigstar)".
    iPoseProof (inFP_domm with "[$] [$]") as "%".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)". iExists hγ, I. iFrame "∗".
    iIntros (C') "((HI & Hglob & Hks & Hdom) & H)".
    iExists hγ, I. iFrame "∗". by iApply "Hbigstar".
  Qed.

  Lemma ghost_heap_sync γ_gh n γ_hn γ_hn' γ_in γ_in' :
    own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]})
      -∗ own γ_gh (◯ {[n := to_agree (γ_hn', γ_in')]})
          -∗ ⌜γ_hn = γ_hn'⌝ ∗ ⌜γ_in = γ_in'⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H".
    iPoseProof (own_valid with "H") as "Valid".
    iDestruct "Valid" as %Valid.
    rewrite auth_frag_valid in Valid *; intros Valid.
    apply singleton_valid in Valid.
    apply to_agree_op_inv in Valid.
    apply leibniz_equiv in Valid.
    inversion Valid.
    by iPureIntro.
  Qed.

  Lemma node_nodeFull_equal γ_I γ_f γ_k γ_gh γ_hn γ_in n In Cn :
    node n In Cn -∗ 
      own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}) -∗ 
        own (γ_hn) (to_frac_agree (1/2) In) -∗ 
          nodeFull γ_I γ_f γ_k γ_gh n -∗ 
            ((lockR true n (∃ In Cn, nodePred γ_f γ_gh γ_k n In Cn)) 
              ∗ node n In Cn ∗ own (γ_hn) (to_frac_agree (1/2) In)
              ∗ nodeShared γ_I γ_gh n In).
  Proof.
    iIntros "Hn #Hgh HhIn Hnf".
    iDestruct "Hnf" as (b In' Cn') "(Hlock & Hns)". 
    destruct b.
    - (* Case n locked *)
      iFrame "Hlock".
      iDestruct "Hns" as (γ_hn' γ_in')"(Hns & HhIn' & HdomIn & Hinr & #Hgh')".
      iPoseProof (ghost_heap_sync _ _ _ _ with "[$Hgh] [$Hgh']") as "(% & %)". subst γ_hn' γ_in'.
      iPoseProof (frac_int_equal with "[$] [$]") as "%". subst In'.
      iFrame "∗". iExists γ_hn, γ_in. iFrame "∗#".
    - (* Case n unlocked: impossible *)
      iDestruct "Hlock" as "(H & Hnp)".
      iDestruct "Hnp" as (? ?)"(Hn' & _)".
      iExFalso. iApply (node_sep_star n In In' with "[$]").
  Qed.

  Lemma CSS_unfold_node_wand γ_I γ_f γ_k γ_gh γ_hn γ_in r C n In Cn :
    CSS γ_I γ_f γ_k γ_gh r C -∗ 
      node n In Cn -∗ own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}) -∗
        own (γ_hn) (to_frac_agree (1/2) In) -∗ 
          inFP γ_f n -∗ 
            (∃ hγ I, node n In Cn 
                  ∗ own (γ_hn) (to_frac_agree (1/2) In)
                  ∗ globalGhost γ_I γ_k γ_f γ_gh hγ r I C
                  ∗ (lockR true n (nodePred γ_f γ_gh γ_k n In Cn)) 
                  ∗ nodeShared γ_I γ_gh n In
                  ∗ (∀ C', globalGhost γ_I γ_k γ_f γ_gh hγ r I C' 
                            ∗ nodeFull γ_I γ_f γ_k γ_gh n -∗ 
                                CSS γ_I γ_f γ_k γ_gh r C')).
  Proof.
    iIntros "Hcss Hn #Hgh HhIn #Hfp".
    iPoseProof (CSS_unfold with "[$] [$]") as (hγ I) "(Hg & Hnf & Hcss')".
    iExists hγ, I.
    iPoseProof (node_nodeFull_equal with "[$] [$] [$] [$]")
      as "(Hlock & H' & Hn & Hn')". 
    iDestruct "Hlock" as "(Hlock' & H)".
    iFrame.
  Qed.

  Lemma CSS_unfold_node γ_I γ_f γ_k γ_gh γ_hn γ_in r C n In Cn :
    CSS γ_I γ_f γ_k γ_gh r C -∗ 
      node n In Cn -∗ own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}) -∗
        own (γ_hn) (to_frac_agree (1/2) In) -∗ 
          inFP γ_f n -∗ 
            (∃ hγ I, node n In Cn ∗ own (γ_hn) (to_frac_agree (1/2) In)
                  ∗ globalGhost γ_I γ_k γ_f γ_gh hγ r I C
                  ∗ lockR true n (∃ In Cn, nodePred γ_f γ_gh γ_k n In Cn)
                  ∗ nodeShared γ_I γ_gh n In
                  ∗ ([∗ set] n' ∈ (domm I ∖ {[n]}), nodeFull γ_I γ_f γ_k γ_gh n')).
  Proof.
    iIntros "Hcss Hn #Hgh HhIn #Hfp".
    iDestruct "Hcss" as (hγ I) "(Hgl & Hbigstar)".
    iPoseProof (inFP_domm with "[$] [$]") as "%".
    rewrite (big_sepS_delete _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hnf & Hbigstar)".
    iPoseProof (node_nodeFull_equal with "[$] [$] [$] [$]")
      as "(Hlock & Hn & HhIn &Hns)".
    iExists hγ, I. iFrame.
  Qed.

  Lemma inInr_impl_inset γ_I γ_f γ_k γ_gh γ_hn γ_in r C n In Cn k :
    CSS γ_I γ_f γ_k γ_gh r C -∗ 
      nodePred γ_f γ_gh γ_k n In Cn -∗
        own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}) -∗ 
          inInr γ_in k -∗ ⌜in_inset K k In n⌝.
  Proof.
    iIntros "Hcss Hnp #Hgh' Hinr".
    iDestruct "Hnp" as (γ_hn' γ_in')"(Hn & HnhIn & HkIn & #Hinfp & #Hgh)".
    iPoseProof (ghost_heap_sync _ _ _ _ with "[$Hgh] [$Hgh']") as "(% & %)". 
    subst γ_hn' γ_in'.
    iPoseProof (CSS_unfold_node with "[$] [$] [$] [$] [$]")
      as (hγ I) "(Hn & HhIn & Hg & Hlock & Hns & Hcss')".
    iDestruct "Hg" as "(HI & Hglob & Hks & Hdom & Hγ)".
    iDestruct "Hns" as (γ_hn' γ_in')"(HIn & HhIn' & HdomIn & Hins & #Hgh'')".
    iDestruct "Hinr" as (R) "(Hinr & %)".
    iPoseProof (ghost_heap_sync _ _ _ _ with "[$Hgh] [$Hgh'']") as "(% & %)". 
    subst γ_hn' γ_in'.
    iPoseProof ((auth_own_incl (γ_in) (inset K In n) R) with "[$]")
      as "incl".
    iDestruct "incl" as %incl. iPureIntro.
    apply gset_included in incl. set_solver.
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

  (* Can we unify this with the above? *)
  Lemma ghost_snapshot_fp_k γ_in (Ks: gset K) k :
    ⊢ own (γ_in) (● Ks) -∗ ⌜k ∈ Ks⌝ ==∗ own (γ_in) (● Ks) ∗ inInr γ_in k.
  Proof.
    iIntros.
    iMod (own_update (γ_in) (● Ks) (● Ks ⋅ ◯ Ks) with "[$]")
      as "H".
    { apply auth_update_frac_alloc. apply gset_core_id. done. }
    iDestruct "H" as "(Haa & Haf)". iFrame. iModIntro.
    iExists Ks. by iFrame.
  Qed.
    
  Lemma ghost_update_step γ_I γ_f γ_k γ_gh r C n In Cn k n' :
    ⊢ CSS γ_I γ_f γ_k γ_gh r C
      -∗ nodePred γ_f γ_gh γ_k n In Cn
      -∗ ⌜in_inset K k In n⌝
      -∗ ⌜in_outset K k In n'⌝
      ==∗ ∃ γ_hn' γ_in', CSS γ_I γ_f γ_k γ_gh r C ∗ nodePred γ_f γ_gh γ_k n In Cn
      ∗ own γ_gh (◯ {[n' := to_agree (γ_hn', γ_in')]}) 
      ∗ inFP γ_f n' ∗ inInr γ_in' k.
  Proof.
    iIntros "Hcss Hnp % %".
    iDestruct "Hnp" as (γ_hn γ_in)"(Hn & HnhIn & HkIn & #Hinfp & #Hgh)".
    iPoseProof (CSS_unfold_node with "[$] [$] [$] [$] [$]")
      as (hγ I) "(Hn & HhIn & (HI & % & Hks & Hdom & Hγ) & Hlock & Hns & Hbigstar)".
    iDestruct "Hns" as (γ_hn' γ_in')"(HIn & HhInn & % & Hins & #Hgh')".
    iPoseProof (ghost_heap_sync _ _ _ _ with "[$Hgh] [$Hgh']") as "(% & %)". 
    subst γ_hn' γ_in'.    
    (* In ≼ I *)
    iPoseProof ((auth_own_incl γ_I I In) with "[$]")
      as (Io) "#incl".
    iDestruct "incl" as %incl.
    (* Some validities we'll use later *)
    iPoseProof (own_valid with "HI") as "%".
    iPoseProof (own_valid with "HIn") as "%".
    (* Prove the preconditions of ghost_snapshot_fp *)
    assert (n' ∈ domm Io). 
    { apply (flowint_step I In Io k); try done.
      by apply auth_auth_valid.
      unfold globalinv in H2. destruct H2 as (_ & _ & cI & _).
      done.
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
    (* unroll star again using n' ∈ domm Io and get In' *)
    assert (n' ∈ domm I ∖ {[n]}). {
      assert (n' ∉ domm In). {
        apply (outset_distinct In n').
        split. by apply auth_frag_valid.
        exists k. done.
      }
      set_solver.
    }
    rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n'); last by eauto.
    iDestruct "Hbigstar" as "(Hnf' & Hbigstar)".
    (* Get ✓ (In ⋅ In') *)
    iDestruct "Hnf'" as (b In' Cn') "(? & HInn)".
    iClear "Hgh'".
    iDestruct "HInn" as (γ_hn' γ_in') "(HInn & (HIn' & % & Hins' & #Hgh'))".
    iAssert (✓ (In ⋅ In'))%I as "%". {
      iPoseProof ((own_op γ_I (◯ In) (◯ In' )) with "[HIn HInn]") as "H";
        first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". iPureIntro.
      apply auth_frag_valid. rewrite auth_frag_op. done.
    }
    (* Use that with flowint_inset_step to get k ∈ inset In' *)
    assert (k ∈ inset K In' n'). {
      apply (flowint_inset_step In In' k n'). done.
      set_solver. set_solver.
    }
    (* snapshot In' inreach to get inInr k n' *)
    iMod (ghost_snapshot_fp_k γ_in' _ k with "[$] [% //]")
      as "(Hins' & #Hininr')".
    (* Aaaand, we're done *)
    iModIntro.
    iAssert (CSS γ_I γ_f γ_k γ_gh r C)%I with "[-Hn HkIn HhInn]" as "Hcss". 
    {
      iExists hγ, I. iFrame "HI Hks Hdom Hγ".
      iSplitR. by iPureIntro.
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iSplitL "Hlock HIn HhIn Hins".
      iExists true, In, Cn. iSplitR "HIn HhIn Hins". eauto with iFrame. 
      iExists γ_hn, γ_in. iFrame "∗%#".
      rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n'); last by eauto.
      iFrame "Hbigstar".
      iExists b, In', Cn'. iSplitR "HIn' Hins' HInn". eauto with iFrame.
      iFrame "%". iExists γ_hn', γ_in'. iFrame "∗#". 
    }
    iExists γ_hn', γ_in'. iFrame "#". iFrame "∗". iExists γ_hn, γ_in. 
    iFrame "#∗".
  Qed.

  Lemma ghost_update_root γ_I γ_f γ_k γ_gh r C k :
    ⊢ CSS γ_I γ_f γ_k γ_gh r C -∗ ⌜k ∈ KS⌝
      ==∗
      ∃ γ_hr γ_ir, CSS γ_I γ_f γ_k γ_gh r C
        ∗ own γ_gh (◯ {[r := to_agree (γ_hr, γ_ir)]}) 
        ∗ inFP γ_f r ∗ inInr γ_ir k.
  Proof.
    iIntros "Hcss %".
    (* Open CSS to get r ∈ domm I *)
    iDestruct "Hcss" as (hγ I) "((HI & #Hglob & Hks & Hdom & Hγ) & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    assert (r ∈ domm I)%I as Hroot.
    { apply globalinv_root_fp. done. }
    (* Snapshot FP for inFP: *)
    iMod (ghost_snapshot_fp γ_f (domm I) r with "[$Hdom] [% //]")
        as "(Hdom & #Hinfp)".
    (* Unfold bigstar *)
    rewrite (big_sepS_elem_of_acc _ (domm I) r); last by eauto.
    iDestruct "Hbigstar" as "(Hnf & Hbigstar)".
    iDestruct "Hnf" as (b Ir Cr) "(Hlock & Hnp)".
    iDestruct "Hnp" as (γ_hr γ_ir)"(HIn & HhInn & % & Hins & #Hgh)".
    (* Get Ir ≼ I needed for globalinv_root_ins *)
    iPoseProof (auth_own_incl _ I Ir with "[$HI $HIn]") as "%".
    iMod (own_update (γ_ir) _ (● (inset K Ir r) ⋅ ◯ (inset K Ir r))
            with "Hins") as "(Hins & #Hinr)".
    { apply auth_update_frac_alloc. apply gset_core_id. done. }
    (* Hksr -> Hinr *)
    iAssert (inInr γ_ir k)%I as "#Hininr".
    {
      iExists (inset K Ir r). iFrame "Hinr". iPureIntro.
      apply (globalinv_root_ins I). done. 
    }
    iModIntro. iExists γ_hr, γ_ir. iSplitL. 
    iExists hγ, I. iFrame "∗". iSplitR; first by iPureIntro.
    iApply "Hbigstar". iExists b, Ir, Cr. iFrame "∗".
    iFrame "%". iExists γ_hr, γ_ir. iFrame "∗#". iFrame "∗#".
  Qed.

  (** High-level lock specs *)

  Lemma lockNode_spec_high γ_I γ_f γ_k γ_gh r n :
    ⊢ inFP γ_f n
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_gh r C >>>
           lockNode #n @ ⊤
         <<< ∃ In Cn, CSS γ_I γ_f γ_k γ_gh r C
                      ∗ nodePred γ_f γ_gh γ_k n In Cn,
             RET #() >>>.
  Proof.
    iIntros "#HFp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iPoseProof (CSS_unfold with "[$] [$]")
      as (hγ I) "(Hg & Hn & Hcss')".
    iSpecialize ("Hcss'" $! C).
    iDestruct "Hn" as (b In Cn) "(Hlock & Hns)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iPoseProof ("Hcss'" with "[-]") as "Hcss".
      { iFrame. iExists b, In, Cn. iFrame. }
       iFrame "Hcss". iIntros "AU". by iModIntro.
    }
    iIntros "Hlockn". iModIntro.
    iDestruct "Hlockn" as "(Hlock & Hnp)".
    iExists In, Cn.
    iPoseProof ("Hcss'" with "[-Hnp]") as "Hcss".
    { iFrame. iExists true, In, Cn. iFrame. }
    iFrame "∗". iIntros "H". by iModIntro.
  Qed.
  
  Lemma unlockNode_spec_high γ_I γ_f γ_k γ_gh r n In Cn :
    ⊢ nodePred γ_f γ_gh γ_k n In Cn
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_gh r C >>>
           unlockNode #n @ ⊤
         <<< CSS γ_I γ_f γ_k γ_gh r C, RET #() >>>.
  Proof.
    iIntros "Hnp". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hnp" as (γ_hn γ_in) "(Hn & HnhIn & HkIn & #Hinfp & #Hgh)".
    iPoseProof (CSS_unfold_node_wand with "[$] [$] [$] [$] [$]")
      as (Hγ I) "(Hn & HhIn & Hg & Hlock & Hns & Hcss')".
    iAssert (nodePred γ_f γ_gh γ_k n In Cn)%I 
        with "[Hn HkIn HhIn]" as "Hnp".
    { iFrame "∗%#". iExists γ_hn, γ_in. iFrame "∗#". }
    iCombine "Hlock" "Hnp" as "HPre".  
    iAaccIntro with "HPre".
    { iIntros "(Hlock & Hnp)". iModIntro.
      iSplitR "Hnp".
      iApply "Hcss'". iFrame. iExists true, In, Cn. iFrame.
      eauto with iFrame.
    }
    iIntros "Hlock". iModIntro.
    iPoseProof ("Hcss'" with "[-]") as "Hcss".
    { iFrame. iExists false, In, Cn. iFrame. }
    iFrame. iIntros "H". by iModIntro.
 Qed.

  (** Proofs of traverse and CSSOp *)

  Theorem create_spec :
   ⊢ {{{ True }}}
        create #()
     {{{ γ_I γ_f γ_k γ_gh (r: Node), RET #r; CSS γ_I γ_f γ_k γ_gh r ∅ }}}.
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
    iMod (own_alloc (● (domm Ir) ⋅ ◯ (domm Ir))) 
          as (γ_f)"(Hf & #Hf')". 
    { apply auth_both_valid_discrete. try done. }
    iMod (own_alloc (to_frac_agree (1) Ir)) 
          as (γ_hr)"HhIn". { try done. }
    iEval (rewrite <-Qp_half_half) in "HhIn".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "HhIn". 
    iDestruct "HhIn" as "(HhIn & HhIn')".
    iMod (own_alloc (● inset K Ir r)) 
          as (γ_ir)"HInr". { apply auth_auth_valid. try done. }
    iMod (own_alloc (● {[r := to_agree (γ_hr, γ_ir)]} 
                      ⋅ ◯ {[r := to_agree (γ_hr, γ_ir)]}  ) ) 
          as (γ_gh)"(Hgh● & #Hgh◯)". 
    { apply auth_both_valid_discrete. split; try done.
      apply singleton_valid. try done. }
    iModIntro. wp_pures.
    iModIntro. iApply ("HΦ" $! γ_I γ_f γ_k γ_gh r).
    iExists {[r := to_agree (γ_hr, γ_ir)]}, Ir. iFrame. iSplitR.
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
      iSplitL "HhIn Hks◯". iExists γ_hr, γ_ir.   
      rewrite Hkeyset. iFrame "∗#". iExists {[r]}. iFrame "#".
      by iPureIntro; clear; set_solver.
      iExists γ_hr, γ_ir. iFrame "∗#".  
  Qed.

  Lemma traverse_spec γ_I γ_f γ_k γ_gh γ_hn γ_in (r: Node) (k: K) (n: Node) :
    ⊢ ⌜k ∈ KS⌝ -∗ inFP γ_f n -∗ 
        own γ_gh (◯ {[n := to_agree (γ_hn, γ_in)]}) -∗ inInr γ_in k -∗
        <<< ∀ C, CSS γ_I γ_f γ_k γ_gh r C >>>
            traverse #n #k @ ⊤
        <<< ∃ (n': Node) (In': multiset_flowint_ur K) (Cn': gset K),
            CSS γ_I γ_f γ_k γ_gh r C
            ∗ nodePred γ_f γ_gh γ_k n' In' Cn'
            ∗ ⌜in_inset K k In' n'⌝ ∗ ⌜¬in_outsets K k In'⌝,
            RET #n'
        >>>.
  Proof.
    iLöb as "IH" forall (n γ_hn γ_in). iIntros "% #Hinfp #Hgh #Hininr".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply lockNode_spec_high; first done.
    (* Open AU to get lockNode pre *)
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C) "Hcss".
    iAaccIntro with "Hcss".
    { iIntros "H". iModIntro. iFrame. iIntros. iModIntro. iFrame. }
    iIntros (In Cn) "(Hcss & Hnp)". iModIntro.
    (* Before closing AU, use CSS to get findNext pre *)
    iPoseProof (inInr_impl_inset with "[$] [$] [$] [$]")
      as "%".
    (* Close AU and move on *)
    iFrame. iIntros "AU". iModIntro.
    wp_pures.
    iDestruct "Hnp" as (γ_hn' γ_in')"(Hn & HnhIn & HkIn & _ & #Hgh')".
    iPoseProof (ghost_heap_sync _ _ _ _ with "[$Hgh] [$Hgh']") as "(% & %)". 
    subst γ_hn' γ_in'.    
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n k In Cn) with "[$Hn]").
    { iPureIntro; split; done. }
    iIntros (b n') "(Hn & Hout)". destruct b.
    - (* Case: findNext returns Some n' *)
      wp_pures. wp_bind (unlockNode _).
      iDestruct "Hout" as %Hout.
      (* Fold nodePred again *)
      iAssert (nodePred γ_f γ_gh γ_k n In Cn)%I
        with "[Hn HnhIn HkIn Hinfp]" as "Hnp".
      { iExists γ_hn, γ_in. iFrame "∗#". }
      (* Get traverse's pre before giving up (node n) when calling unlock *)
      iApply fupd_wp. clear C. iMod "AU" as (C) "[Hcss [Hclose _]]".
      iClear "Hgh'".
      iMod (ghost_update_step with "[$] [$] [% //] [% //]")
        as (γ_hn' γ_in')"(Hcss & Hnp & Hgh' & Hinfp' & Hininr')".
      (* Close AU after getting traverse's pre *)
      iMod ("Hclose" with "Hcss") as "AU". clear C. iModIntro.
      awp_apply (unlockNode_spec_high with "Hnp").
      (* Open AU for unlockNode's pre *)
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C) "Hcss".
      iAaccIntro with "Hcss".
      { iIntros. iModIntro. iFrame. iIntros "AU". iModIntro. iFrame. }
      (* The last line should really be a tactic.. *)
      iIntros "Hcss". iModIntro.
      (* Close up AU again *)
      iFrame. iIntros "AU". iModIntro. 
      wp_pures. iSpecialize ("IH" $! n').
      iApply ("IH" with "[% //] [$] [$] [$]"). done.
    - (* Case: findNext returns None *)
      (* Open AU and commit *)
      iApply fupd_wp. clear C. iMod "AU" as (C) "[Hcss [_ Hclose]]".
      iSpecialize ("Hclose" $! n In Cn).
      iAssert (nodePred γ_f γ_gh γ_k n In Cn)%I
        with "[Hn HnhIn HkIn Hinfp]" as "Hnp".
      { iExists γ_hn, γ_in. iFrame "∗#". }
      iMod ("Hclose" with "[$Hcss $Hnp $Hout]") as "HΦ"; first by iPureIntro.
      iModIntro. wp_pures. done.
  Qed.

  (** Verification of abstract specification of the search structure operation. *)
    
  Theorem CSSOp_spec γ_I γ_f γ_k γ_gh r (k: K) (dop: dOp):
    ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_gh r C >>>
      CSSOp dop r #k @ ⊤
    <<< ∃ C' (res: bool), CSS γ_I γ_f γ_k γ_gh r C'
        ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". iLöb as "IH". wp_lam.
    (* Open AU for traverse's pre *)
    iApply fupd_wp. iMod "AU" as (?) "[Hcss [Hclose _]]".
    iMod (ghost_update_root with "[$] [% //]") as (γ_hr γ_ir) "(Hcss & #Hghr & #inFP_r & #inInr_k)".
    iMod ("Hclose" with "[$] ") as "AU".
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec with "[% //] [$] [$]"); try done.
    (* Open AU for traverse's atomic pre *)
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (?) "Hcss".
    iAaccIntro with "Hcss"; first by eauto with iFrame.
    (* Get traverse's post and close AU *)
    iIntros (n In Cn) "(Hcss & Hnp & Hinset & Hnotout)".
    iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnp" as (γ_hn γ_in)"(Hn & HnhIn & HkIn & #Hinfp & #Hgh)".
    wp_apply (decisiveOp_spec with "[$Hn]"); first by iPureIntro.
    iIntros (b res Cn'). iIntros "(Hn & Hb)". destruct b.
    - (* Case: decisiveOp succeeds *)
      iDestruct "Hb" as "#HΨ".
      wp_pures. wp_bind(unlockNode _)%E.
      (* Note: cannot use unlockNode_spec_high here because 
         that needs nodePred, which we won't have until we linearize,
         which we can't do until we open the AU.
         We can't open the AU before unlockNode, because linearizing will
         mean committing the AU and giving up CSS (needed by unlockNode).
         So we manually execute unlockNode_spec and linearize simultaneously.
         TODO: would it work if nodePred was inside atomic pre of lockNode?
       *)
      awp_apply (unlockNode_spec_low n).
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (C) "Hcss".
      (* Now unfold CSS to execute unlockNode *)
      iPoseProof (CSS_unfold_node_wand with "[$] [$] [$] [$] [$]")
        as (Hγ I) "(Hn & HhIn & Hg & Hlock & Hns & Hcss')".
      iDestruct "Hlock" as "(Hlock & _)".
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro.
        iPoseProof ("Hcss'" with "[-Hn HhIn HkIn]") as "Hcss".
        { iFrame. iExists true, In, Cn. iFrame. }
        iFrame "Hcss". iIntros "AU". iModIntro. iFrame "∗ #". 
      }
      iIntros "Hlock". (* unlockNode finished executing *)
      (* Linearization Point *)
      iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C)
              with "[HkIn Hks]") as (C') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "HkIn") as "%".
        assert (k ∈ keyset K In n); first by apply keyset_def.
        iAssert (⌜Cn' ⊆ keyset K In n⌝)%I with "[HΨ]" as "%".
        { iDestruct "HΨ" as "%". iPureIntro.
          apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done.
        }
        iFrame "∗ #". by iPureIntro.
      }
      (* Close everything up, return *)
      iModIntro. iExists C', res. iSpecialize ("Hcss'" $! C').
      iPoseProof ("Hcss'" with "[-]") as "Hcss".
      { iFrame "∗". iExists false, In, Cn'. iFrame "∗#%".
        iExists γ_hn, γ_in. iFrame "∗#". }
      iFrame "Hcss HΨC". iIntros "H". iModIntro. wp_pures. done.
    - (* Case: decisiveOp fails *)
      wp_pures. iDestruct "Hb" as "%". subst Cn'.
      iAssert (nodePred γ_f γ_gh γ_k n In Cn)%I
        with "[Hn HnhIn HkIn Hinfp]" as "Hnp".
      { iExists γ_hn, γ_in. iFrame "∗#". }
      awp_apply (unlockNode_spec_high with "Hnp").
      (* Open AU for unlockNode's pre *)
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C) "Hcss".
      iAaccIntro with "Hcss".
      { iIntros. iModIntro. iFrame. iIntros "AU". iModIntro. iFrame. }
      iIntros "Hcss". iModIntro.
      (* Close up AU again *)
      iFrame. iIntros "AU". iModIntro. 
      wp_pures. by iApply "IH".
  Qed.

End Link_Template.

From stdpp Require Export gmap pmap.
From Coq Require Import PArith.
Require Import Coq.Setoids.Setoid.

(** Extend stdpp's gmap with a merge function where the merge operation also depends on the key and not just the merged values. *)

Fixpoint Poimap_raw {A B} (f : positive → A → option B) (t : Pmap_raw A) : Pmap_raw B :=
  match t with
  | PLeaf => PLeaf
  | PNode o l r => PNode' (o ≫= f xH) (Poimap_raw (f ∘ xO) l) (Poimap_raw (f ∘ xI) r)
  end.

Lemma f_odd: forall A (i: positive) (f: positive -> A), f (i~1%positive) = (f ∘ xI) i.
Proof.
  intros.
  unfold compose.
  reflexivity.
Qed.

Lemma f_even: forall A (i: positive) (f: positive -> A), f (i~0%positive) = (f ∘ xO) i.
Proof.
  intros.
  unfold compose.
  reflexivity.
Qed.

Lemma Poimap_wf {A B} (f : positive → A → option B) t : Pmap_wf t → Pmap_wf (Poimap_raw f t).
Proof. revert f. induction t.
       - simpl. eauto.
       - simpl. eauto.
         intro.
         intro.
         unfold PNode'.
         assert (Pmap_wf t2).
         unfold Pmap_wf in H.
         { destruct o.
           + unfold andb in H.
             destruct (_ A t2).
             auto.
             destruct (_ A t1).
             contradiction.
             contradiction.
           + destruct t2.
             auto.
             destruct t1.
             unfold andb in H at 1.
             apply H.
             destruct (match o0 with | Some _ => _ | None => _ end).
             simpl in H.
             apply H.
             simpl in H.
             contradiction.
         }
         assert (Pmap_wf t1).
         unfold Pmap_wf in H.
         destruct o.
         + unfold andb in H.
           destruct (_ A t1).
           auto.
           contradiction.
         + destruct t1.
           destruct t2.
           contradiction.
           auto.
           destruct (_ A t2).
           simpl in H.
           unfold Pmap_wf.
           unfold andb in H at 1.
           destruct (match o with | Some _ => _ | None => _ end).
           auto.
           contradiction.
           unfold andb in H at 1.
           destruct (match o with | Some _ => _ | None => _ end).
           contradiction.
           contradiction.
         + assert (Pmap_wf (Poimap_raw (f ∘ xO) t1)).
           apply IHt1.
           apply H1.
           assert (Pmap_wf (Poimap_raw (f ∘ xI) t2)).
           apply IHt2.
           apply H0.
           { destruct (Poimap_raw (f ∘ xO) t1).
             - destruct (o ≫= f 1%positive).
               unfold Pmap_wf.
               apply IHt2.
               apply H0.
               destruct (Poimap_raw (f ∘ xI) t2).
               auto.
               simpl.
               apply H3.
             - unfold Pmap_wf.
               simpl.
               destruct (o ≫= f 1%positive).
               unfold andb.
               unfold Pmap_wf in H2.
               destruct (match o0 with | Some _ => _ | None => _ end).
               apply H3.
               contradiction.
               unfold andb.
               unfold Pmap_wf in H2.
               unfold Pmap_wf in H2.
               destruct (match o0 with | Some _ => _ | None => _ end).
               apply H3.
               contradiction.
           }
Qed.

Lemma Poimap_lookup {A B} (f : positive → A → option B) t i :
  Poimap_raw f t !! i = t !! i ≫= f i.
Proof.
  revert f. revert i. induction t as [|o l IHl r IHr]; intros [i|i|]; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + intro. rewrite ?PNode_lookup. simpl.
      assert (f (i~1%positive) = (f ∘ xI) i).
      unfold compose.
      reflexivity.
      rewrite H. auto.
    + intro. rewrite ?PNode_lookup. simpl.
      assert (f (i~0%positive) = (f ∘ xO) i).
      unfold compose.
      reflexivity.
      rewrite H. auto.
    + intro. rewrite ?PNode_lookup. simpl. auto.
Qed.

Fixpoint Pimerge_raw {A B C} (f : positive → option A → option B → option C)
           (t1 : Pmap_raw A) (t2 : Pmap_raw B) : Pmap_raw C :=
  match t1, t2 with
  | PLeaf, t2 => Poimap_raw (λ i, f i None ∘ Some) t2
  | t1, PLeaf => Poimap_raw (λ i, flip (f i) None ∘ Some) t1
  | PNode o1 l1 r1, PNode o2 l2 r2 =>
    PNode' (f xH o1 o2) (Pimerge_raw (f ∘ xO) l1 l2) (Pimerge_raw (f ∘ xI) r1 r2)
  end.


Lemma Pimerge_wf {A B C} (f : positive → option A → option B → option C) t1 t2 :
  Pmap_wf t1 → Pmap_wf t2 → Pmap_wf (Pimerge_raw f t1 t2).
Proof.
  revert f. revert t2. induction t1.
  - intros.
    apply Poimap_wf. auto.
  - intros.
    eauto.
    simpl.
    assert (Pmap_wf t1_1).
    revert H.
    apply Pmap_wf_l.
    assert (Pmap_wf t1_2).
    revert H.
    apply Pmap_wf_r.
    unfold Pmap_wf in H.
    destruct t2;
      unfold PNode'.
    assert (Pmap_wf (Poimap_raw ((λ i : positive, flip (f i) None ∘ Some) ∘ xO)
                                t1_1)).
    apply Poimap_wf.
    auto.
    assert (Pmap_wf (Poimap_raw ((λ i : positive, flip (f i) None ∘ Some) ∘ xI)
                                t1_2)).
    apply Poimap_wf.
    auto.

    +  destruct (Poimap_raw ((λ i : positive, flip (f i) None ∘ Some) ∘ xO)
                            t1_1).
       destruct (o ≫= flip (f 1%positive) None ∘ Some);
         unfold Pmap_wf.
       rewrite ?andb_True.
       eauto using Poimap_wf.
       destruct (Poimap_raw ((λ i : positive, flip (f i) None ∘ Some) ∘ xI)
                            t1_2).
       auto.
       rewrite ?andb_True.
       auto.
       eauto using Poimap_wf.
       unfold Pmap_wf.
       destruct (o ≫= flip (f 1%positive) None ∘ Some);
         unfold Pmap_wf.
       rewrite ?andb_True.
       eauto.
       rewrite ?andb_True.
       eauto.
    + assert (Pmap_wf  (Pimerge_raw (f ∘ xO) t1_1 t2_1)).
      apply IHt1_1.
      auto.
      revert H0.
      apply Pmap_wf_l.
      destruct (Pimerge_raw (f ∘ xO) t1_1 t2_1).
      destruct (f 1%positive o o0).
      unfold Pmap_wf.
      rewrite ?andb_True.
      split.
      trivial.
      apply IHt1_2.
      auto.
      revert H0.
      apply Pmap_wf_r.
      assert (Pmap_wf  (Pimerge_raw (f ∘ xI) t1_2 t2_2)).
      apply IHt1_2.
      auto.
      revert H0.
      apply Pmap_wf_r.
      unfold Pmap_wf.
      destruct (Pimerge_raw (f ∘ xI) t1_2 t2_2).
      trivial.
      rewrite ?andb_True.
      split.
      trivial.
      apply H4.
      assert (Pmap_wf  (Pimerge_raw (f ∘ xI) t1_2 t2_2)).
      apply IHt1_2.
      auto.
      revert H0.
      apply Pmap_wf_r.
      destruct (Pimerge_raw (f ∘ xI) t1_2 t2_2).
      unfold Pmap_wf.
      destruct (f 1%positive o o0).
      rewrite ?andb_True.
      auto.
      rewrite ?andb_True.
      auto.
      unfold Pmap_wf.
      destruct (f 1%positive o o0).
      rewrite ?andb_True.
      split.
      apply H3.
      apply H4.
      rewrite ?andb_True.
      split.
      apply H3.
      apply H4.
Qed.

Lemma Pimerge_lookup {A B C} (f : positive → option A → option B → option C)
    (Hf : ∀ i, f i None None = None) t1 t2 i :
  Pimerge_raw f t1 t2 !! i = f i (t1 !! i) (t2 !! i).
Proof.
  revert Hf. revert f t2 i. induction t1 as [|o1 l1 IHl1 r1 IHr1]; intros f t2 i Hf; unfold Pimerge_raw. simpl.
  { rewrite Poimap_lookup. by destruct (t2 !! i). }
  unfold flip.
  destruct t2 as [|l2 o2 r2]. rewrite Poimap_lookup.
  destruct (PNode o1 l1 r1 !! i); simpl.
  - unfold lookup, Plookup_raw. reflexivity.
  - unfold lookup, Plookup_raw. rewrite Hf. reflexivity.
  - destruct i; rewrite PNode_lookup; unfold lookup, Plookup_raw.
    * rewrite f_odd.
      apply IHr1.
      intro. unfold compose. apply Hf.
    * rewrite f_even.
      apply IHl1.
      intro. unfold compose. apply Hf.
    * auto.
Qed.

Arguments PMap {_} _ _ : assert.

Class Imerge (M : Type → Type) K `{Countable K, (∀ (T: Type), Lookup K T (M T))} :=
  IMerge
  {
    imerge {A B C} (f : K → option A → option B → option C) (m1 : M A) (m2 : M B) : M C;
    imerge_prf {A B C} (f : K → option A → option B → option C) (m1 : M A) (m2 : M B) (i : K):
      (∀ j, f j None None = None) -> imerge f m1 m2 !! i = f i (m1 !! i) (m2 !! i)
  }.

Definition Pimerge {A B C} (f : positive -> option A -> option B -> option C)
           (m1 : Pmap A) (m2 : Pmap B) :=
  let (t1,Ht1) := m1 in let (t2,Ht2) := m2 in PMap _ (Pimerge_wf f _ _ Ht1 Ht2).

Lemma Pimerge_prf {A B C} (f : positive → option A → option B → option C)
    (m1 : Pmap A) (m2 : Pmap B) i (Hf : ∀ i, f i None None = None) :
    Pimerge f m1 m2 !! i = f i (m1 !! i) (m2 !! i).
Proof.
  destruct m1.
  destruct m2.
  apply Pimerge_lookup.
  apply Hf.
Qed.

Instance pmap_positive_imerge : Imerge Pmap positive :=
  {|
    imerge A B C := Pimerge;
    imerge_prf A B C := Pimerge_prf
  |}.

Lemma gmap_imerge_wf `{Countable K} {A B C}
    (f : K → option A → option B → option C) m1 m2 :
  let f' i o1 o2 := match o1, o2 with
                    | None, None => None
                    | _, _ =>
                      decode i ≫= (λ k, f k o1 o2) end
  in
  gmap_wf K m1 → gmap_wf K m2 → gmap_wf K (imerge f' m1 m2).
Proof.
  intros f'; unfold gmap_wf; rewrite !bool_decide_spec.
  intros Hm1 Hm2 p z. unfold imerge; simpl.
  rewrite Pimerge_prf by done; intros.
  destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver.
Qed.

Definition gmap_imerge `{Countable K} {A B C}
           (f : K -> option A -> option B -> option C) (m1 : gmap K A) (m2 : gmap K B)
           : gmap K C :=
  let (m1,Hm1) := m1 in
  let (m2,Hm2) := m2 in
  let f' i o1 o2 := match o1, o2 with
                    | None, None => None
                    | _, _ =>
                      decode i ≫= (λ k, f k o1 o2)
                    end
  in
  GMap (imerge f' m1 m2) (gmap_imerge_wf f m1 m2 Hm1 Hm2).

Lemma gmap_imerge_prf `{Countable K} {A B C} (f : K → option A → option B → option C)
    (m1 : gmap K A) (m2 : gmap K B) i `{∀ i, DiagNone (f i)} :
    gmap_imerge f m1 m2 !! i = f i (m1 !! i) (m2 !! i).
Proof.
  destruct m1 as [p1 ?], m2 as [p2 ?].
  unfold gmap_imerge.
  unfold lookup; simpl.
  unfold DiagNone in H0.
  rewrite Pimerge_prf.
  case (p1 !! encode i).
  all: try rewrite decode_encode; auto.
  case (p2 !! encode i).
  all: auto.
Qed.

Instance gmap_Imerge `{Countable K} : Imerge (gmap K) K :=
  {|
    imerge A B C := gmap_imerge;
    imerge_prf A B C := gmap_imerge_prf
  |}.

Lemma gmap_imerge_empty {A} `{Countable K}
      (f : K → option A → option A → option A)
      : (∀ i y, f i y None = y) -> ∀ m, gmap_imerge f m ∅ = m.
Proof.
  intros Hf m.
  rewrite map_eq_iff.
  intros i.
  rewrite gmap_imerge_prf.
  replace (empty !! i) with (None : option A).
  all: auto.
  unfold DiagNone.
  auto.
Qed.

Lemma map_Forall_True {A} `{Countable K} (m : gmap K A) (p : K -> A -> Prop) :
      (∀ (k : K) (a : A), p k a) → (map_Forall p m).
Proof.
  intros.
  unfold map_Forall.
  intros.
  apply H0.
Qed.


Definition gmap_insert_map {A} `{Countable K} (m s: gmap K A) : (gmap K A) :=
      let f := λ k a m', <[k := a]> m' in
      map_fold f m s.

Lemma gmap_lookup_insert_map_aux {A} `{Countable K} (m s: gmap K A) :
      ∀ k, (k ∈ dom (gset K) s → gmap_insert_map m s !! k = s !! k)
          ∧ (k ∉ dom (gset K) s → gmap_insert_map m s !! k = m !! k).
Proof.
  set (P := λ (m': gmap K A) (X: gmap K A),
              ∀ j, (j ∈ dom (gset K) X → m' !! j = X !! j)
                  ∧ (j ∉ dom (gset K) X → m' !! j = m !! j)).
  apply (map_fold_ind P); try done.
  intros k a m' r Hmi HP. unfold P. unfold P in HP.
  intros j. split.
  - intros Hj. rewrite <-not_elem_of_dom in Hmi.
    rewrite dom_insert in Hj. rewrite elem_of_union in Hj.
    destruct Hj as [Hj | Hj].
    + assert (j = k) by set_solver; subst j.
      by rewrite !lookup_insert.
    + assert (j ≠ k) by set_solver.
      rewrite !lookup_insert_ne; try done.
      by apply HP.
  - intros Hj. rewrite <-not_elem_of_dom in Hmi.
    rewrite dom_insert in Hj.
    assert (j ≠ k) by set_solver. 
    rewrite !lookup_insert_ne; try done. 
    apply HP. set_solver.
Qed.                              

Lemma gmap_lookup_insert_map {A} `{Countable K} (m s: gmap K A) (k: K) :
      k ∈ dom (gset K) s → gmap_insert_map m s !! k = s !! k.
Proof.
  apply gmap_lookup_insert_map_aux.
Qed.

Lemma gmap_lookup_insert_map_ne {A} `{Countable K} (m s: gmap K A) (k: K) :
      k ∉ dom (gset K) s → gmap_insert_map m s !! k = m !! k.
Proof.
  apply gmap_lookup_insert_map_aux.
Qed.

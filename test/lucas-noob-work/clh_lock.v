(* This is material copied from the Diaframe proof of the CLH lock. I add some
annotations here that help tie it to the canonical description of the lock in
Craig's paper "Bulding FIFO and Priority-Queuing Spin Locks from Atomic Swap". *)

From diaframe.heap_lang Require Import proof_automation wp_auto_lob.
From diaframe.lib Require Import own_hints.
From iris.algebra Require Import agree frac excl.

Definition new_lock : val :=
  λ: "_", ref (ref #false).

Definition new_node : val :=
  λ: "_",
    let: "ret" := AllocN #2 NONE in (* NOTE: Nodes in Diaframe, it seems, are tuples --- hence, the AllocN #2. We set both fields here to NONE, then we set the first field to false in the following line. It helps to notice that we are directly referencing memory locations here --- not logical structures at the programming language level ---  so when we set the value at "ret" to be ref #false, we are setting the first memory unit (doesn't really matter, but i.e. would be a byte in a byte-addressable system), or the first field (logically speaking), to false. The second field remains NONE. *)
    "ret" <- ref #false;;
    "ret".

Definition wait_on : val := (* NOTE: This is the spin part of the spinlock. *)
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
    ("node" +ₗ #1) <- "pred";; (* NOTE: Here, we are setting our Request/node state to PENDING (true in Diaframe code). Then, we set the lock's tail (lk) to the pointer to the acquiring Request/node's reference and the acquiring Request/node's predecessor pointer (i.e. the pointer we're watching to determine our place in line) to the lock's tail (the one from before we swapped it out/set it to something else). *)
    wait_on "pred".

Definition release : val :=
  λ: "node",
    ! "node" <- #false;; (* NOTE: false == GRANTED and true == PENDING in Craig's paper. We can interpret false here as false to the statement "waiting to acquire" or "is pending". *)
    "node" <- ! ("node" +ₗ #1). (* NOTE: this step corresponds to the step in Craig's description of grant_lock where the releaser takes ownership of the Request/node granted to it by its predecessor --- in the Diaframe code here, ("node" + #1) is the second field in the node tuple that stores the pointer to the predecessor reference (see line 30 above for the associated operation in acquire) *)

(* NOTE: I guess in this implementation, each calling thread must keep track of its own associated node/Request that it currently owns. It's returned by release though, for example, so it can be reused as long as we save that returned value. *)

(* NOTE: Below, we have the specifications and proofs of the implementation above. *)

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
  (* NOTE: Lemma for a queued location? Not sure what the arguments here mean. Either gamma owns 1.0 of l. Or there is some boolean b s.t. the value at l is b and we own 1/2 of l. Either b is true, which should mean the location is attempting to acquire the lock (?) or b is false (we hold the lock) AND we own resource R, we have exclusive ownership of γe, which I guess is the watched node, l owns 1/2 of γ, which I guess is the owned node, and l also owns half of the state bool of the owned node? *)
  (* NOTE: From the spin_lock.v example, it seems like gamma and gammae should indicate ghost state, particularly a ghost name. How does this make sense here? In spin_lock.v, own gamma (Excl ()) indicates locked gamma, which means that the lock is currently locked/held (as the name suggests lol). In fact, queued_loc looks *a lot* like lock_inv in the spin lock verification --- I believe it serves the same purpose. BTW: each node's first field is a bool for its state and its second field is a pointer to the node it's watching. l should be that first field, i.e. the bool for the state. R is the resource and indicates whether the process that owns the node currently has access to that resource. γe is the ghost name representing the lock itself. γ is the ghost name representing the node itself (the one that's queued). *)
  (* NOTE: I gotta figure out what the left disjoint here means. The right disjoint makes more sense given our deduced interpretation above. When a process queues a location/node, it has 1/2 ownership over it (the points to just means that the first field of the node is the state boolean). If b is true, i.e. we are still pending/in the process of acquiring the lock, that's the whole spec --- the predecessor node's process holds the other 1/2 ownership over our node. If b is false, i.e. we now have the lock, we own R, we have exclusive lock access (own gammae (Excl ())), we also own the other 1/2 of our current node now (since there's no more predecessor node). The question remains: what is the own gammae (to_agree l, ...) stuff doing, both in the left disjunct and in the right disjunct in the b = false branch. *)
  (* NOTE: Also, for this lock, shouldn't we be watching the predecessor's state? The above interpretation makes it seem like we're just looking at our own node's state. *)

  Definition free_node n : iProp Σ :=
    ∃ (l : loc) v, n ↦ #l ∗ (n +ₗ 1) ↦ v ∗ l ↦ #false.
  (* NOTE: l is a location, not sure what v is. n is the node. The first field of the node points to the address of a location l that holds the state value. The second field of the node points to some v...this would generally be the watched node, but it doesn't seem to matter here. the value at l should be false, since this is the default value when a node is first created. *)
  (* NOTE: Being free is the opposite of being queued (i.e. this predicate should be the converse of queued_loc above). *)

  Definition acquired_node γe n R : iProp Σ :=
    ∃ (l p : loc), n ↦ #l ∗ (∃ γ, inv N_node (queued_loc γe l γ R) ∗ own γ (to_agree l, 1/2)%Qp) ∗ l ↦{#1/2} #true ∗
                  (n +ₗ 1) ↦ #p ∗ p ↦ #false ∗ own γe (Excl ()).
  (* NOTE: l and p are both locations. p is the predecessor. n needs to be queued (can't be free?). Like above, first field of n points to address of state location.  *)

  Definition lock_inv γe lk R : iProp Σ :=
    ∃ (l : loc), lk ↦ #l ∗ ∃ γ, own γ (to_agree l, 1/2)%Qp ∗ inv N_node (queued_loc γe l γ R).
  (* NOTE: Lock points to the address of location l. There is some gamma, a ghost name representing a node, that we own 1/2 of and that has value l (note that lk points to the address of l, which would also then be the address of this node). I think thinking through and relating lock_inv to the definition of queued_loc will help me understand what the own γ (to_agree l, 1/2)%Qp stuff is doing. Specifically, the own here makes it so that we cannot take the left disjunct of queued_loc...*)
  (* NOTE: BTW, the fact that we have γe here strongly supports the fact that it is a ghost name representing the lock itself. *)

  Definition is_lock γe R v : iProp Σ :=
    ∃ (lk : loc), ⌜v = #lk⌝ ∗ inv N (lock_inv γe lk R).

  (* These are the specifications for each of the procedure definitions at the top of this file. They are just Hoare triples, using the lemmas we defined just above this. *)
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

  Definition queued_loc γe l γ R : iProp Σ :=
    own γ (to_agree l, 1%Qp) ∨ (∃ (b : bool), l ↦{#1/2} #b ∗ (⌜b = true⌝ ∨ (⌜b = false⌝ ∗ R ∗ own γe (Excl ()) ∗ own γ (to_agree l, 1/2)%Qp ∗ l ↦{#1/2} #b))).
  (* If own γ (to_agree l, 1%Qp) is true, this is the very end/head of the queue, where our process will own the entirety of the node (?). I think this is the crux of a lot of this --- how exactly does queued_loc express the fact that a location/node is queued? A queued location is either inside the queue (waiting to be the head), or at the head. It looks like the first left disjunct is when there is only the lock location in the queue, the b=true branch of the right disjunct is when we are inside the queue, and the b=false branch of the right disjunct is when we are at the head. *)
  (* NOTE: The lock is just the linked list of nodes.  *)

  Definition free_node n : iProp Σ :=
    ∃ (l : loc) v, n ↦ #l ∗ (n +ₗ 1) ↦ v ∗ l ↦ #false.

  Definition acquired_node γe n R : iProp Σ :=
    ∃ (l p : loc), n ↦ #l ∗ (∃ γ, inv N_node (queued_loc γe l γ R) ∗ own γ (to_agree l, 1/2)%Qp) ∗ l ↦{#1/2} #true ∗
                  (n +ₗ 1) ↦ #p ∗ p ↦ #false ∗ own γe (Excl ()).
  (* This formula forces queued_loc to take the b=true path, since the b=false asserts that l ↦{#1/2} #false, while our statement here asserts that l ↦{#1/2} #true. *)

  Definition lock_inv γe lk R : iProp Σ :=
    ∃ (l : loc), lk ↦ #l ∗ ∃ γ, own γ (to_agree l, 1/2)%Qp ∗ inv N_node (queued_loc γe l γ R).

  (* lock --> l, lock owns half of ghost representation of l, l is a queued location. *)

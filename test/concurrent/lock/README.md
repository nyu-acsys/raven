# Lock examples

`queue_lock.rav` defines the shared `QueueLock` contract. `create` establishes
`is_lock(l, r)`. `acquire` returns an abstract guard and the protected resource;
`release` consumes both. Operations reserve the public lock region, with the
implementation's private invariants declared below it.

`clh-lock.rav` and `mcs-lock.rav` implement and seal this interface. Both allocate
fresh nodes on every acquisition: CLH allocates a node wrapper and a waiting
location; MCS allocates one queue node. MCS's signalling tokens are ghost state.
The contract does not return a reusable guard after release. These examples do
not establish physical-node reclamation or unrestricted node reuse across locks.
Private invariant identities retain their lock and resource parameters throughout.

`queue_lock_client.rav` checks a counter client using only the lock functor's
interface. `queue_locks.rav` applies that client to both implementations and
exercises repeated acquisitions. Its cram test verifies both implementations and
the shared client together. Negative tests in `test/ci/back-end/regions/locks`
reject releasing with another lock's guard, releasing twice with the same guard,
and accessing hidden invariants.

The original Iris-derived proofs, including CLH's reusable-node contract, are
preserved in `../../comparison/clh-lock.rav` and `../../comparison/mcs-lock.rav`.

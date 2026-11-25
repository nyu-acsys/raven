  $ dune exec -- raven --shh ./queue_lock_reused_guard.rav
  [Error] File "./queue_lock_reused_guard.rav", line 12, columns 4-27:
  12 |     L.release(l, guard, c);
           ^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "queue_lock.rav", line 21, columns 30-47:
  21 |     requires is_lock(l, r) && held(l, guard, r) && R.resource(r)
                                     ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

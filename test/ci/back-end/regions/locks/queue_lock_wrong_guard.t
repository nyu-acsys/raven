  $ dune exec -- raven --shh ./queue_lock_wrong_guard.rav
  [Error] File "./queue_lock_wrong_guard.rav", line 12, columns 4-31:
  12 |     L.release(other, first, d);
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "queue_lock.rav", line 21, columns 30-47:
  21 |     requires is_lock(l, r) && held(l, guard, r) && R.resource(r)
                                     ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

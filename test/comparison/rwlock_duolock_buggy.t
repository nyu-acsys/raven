  $ dune exec -- raven --shh ./rwlock_duolock_buggy.rav
  [Error] File "./rwlock_duolock_buggy.rav", line 122, columns 4-44:
  122 |     fold LkBResource.resource((l, lkA_ref));
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./rwlock_duolock_buggy.rav", line 34, columns 14-34:
  34 |               tokenCounter(r#0, z) && LkA.locked(r#1)
                     ^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

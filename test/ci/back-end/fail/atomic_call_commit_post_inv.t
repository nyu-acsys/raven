  $ dune exec -- raven --shh ./atomic_call_commit_post_inv.rav
  [Error] File "./atomic_call_commit_post_inv.rav", line 24, columns 2-17:
  24 |   fold pinned(x);
         ^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./atomic_call_commit_post_inv.rav", line 24, columns 2-17:
  24 |   fold pinned(x);
         ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

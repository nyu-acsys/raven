  $ dune exec -- raven --shh ./atomic_call_abort_one_branch.rav
  [Error] File "./atomic_call_abort_one_branch.rav", line 21, columns 4-15:
  21 |     incr(x, y);
           ^^^^^^^^^^^
  Verification Error: This atomic call gives up its ordinary precondition where the atomic update or invariant open around it was opened, which every branch must then do; open it within this branch instead.
  [Error] File "./atomic_call_abort_one_branch.rav", line 19, columns 2-17:
  19 |   unfold cInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [1]

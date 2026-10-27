  $ dune exec -- raven --shh ./atomic_call_abort_ghost_update.rav
  [Error] File "./atomic_call_abort_ghost_update.rav", line 57, columns 2-13:
  57 |   incr(x, y);
         ^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call where the atomic update or invariant open around it was opened, which is where it is given up.
  [Error] File "./atomic_call_abort_ghost_update.rav", line 53, columns 2-23:
  53 |   unfold counterInv(x);
         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [Error] File "./atomic_call_abort_ghost_update.rav", line 31, columns 31-48:
  31 |   requires mailboxInv(y, x) && own(x.g, frag(1))
                                      ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- raven --shh ./atomic_call_abort_unabortable_update.rav
  [Error] File "./atomic_call_abort_unabortable_update.rav", line 25, columns 2-7:
  25 |   p(x);
         ^^^^^
  Verification Error: The atomic update open around this atomic call may not be abortable if the call aborts.
  [Error] File "./atomic_call_abort_unabortable_update.rav", line 23, columns 2-19:
  23 |   n := openAU(phi);
         ^^^^^^^^^^^^^^^^^
  Related Location: This atomic update may not be abortable if the call aborts.
  [Error] File "./atomic_call_abort_unabortable_update.rav", line 19, columns 38-63:
  19 |   atomic requires own(x.c, n, 1.0) && own(x.g, auth_frag(n, n))
                                             ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

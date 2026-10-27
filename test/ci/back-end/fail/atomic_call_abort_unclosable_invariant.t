  $ dune exec -- raven --shh ./atomic_call_abort_unclosable_invariant.rav
  [Error] File "./atomic_call_abort_unclosable_invariant.rav", line 29, columns 2-10:
  29 |   incr(x);
         ^^^^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./atomic_call_abort_unclosable_invariant.rav", line 25, columns 2-23:
  25 |   unfold counterInv(x);
         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./atomic_call_abort_unclosable_invariant.rav", line 15, columns 19-39:
  15 |   exists n: Int :: own(x.count, n, 1.0) && own(x.g, auth_frag(n, n))
                          ^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [Error] File "./atomic_call_abort_unclosable_invariant.rav", line 15, columns 43-68:
  15 |   exists n: Int :: own(x.count, n, 1.0) && own(x.g, auth_frag(n, n))
                                                  ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

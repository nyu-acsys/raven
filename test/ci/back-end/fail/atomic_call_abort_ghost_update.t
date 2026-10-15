  $ dune exec -- raven --shh ./atomic_call_abort_ghost_update.rav
  [Error] File "./atomic_call_abort_ghost_update.rav", line 58, columns 2-13:
  58 |   incr(x, y);
         ^^^^^^^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./atomic_call_abort_ghost_update.rav", line 54, columns 2-23:
  54 |   unfold counterInv(x);
         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./atomic_call_abort_ghost_update.rav", line 22, columns 19-25:
  22 |   exists n: Int :: n >= 0 && own(x.count, n, 1.0) && own(x.g, auth_frag(n, n))
                          ^^^^^^
  Related Location: This assertion may not hold.
  [1]

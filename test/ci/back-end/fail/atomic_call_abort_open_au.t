  $ dune exec -- raven --shh ./atomic_call_abort_open_au.rav
  [Error] File "./atomic_call_abort_open_au.rav", line 36, columns 2-7:
  36 |   p(x);
         ^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./atomic_call_abort_open_au.rav", line 34, columns 2-17:
  34 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./atomic_call_abort_open_au.rav", line 13, columns 19-35:
  13 |   exists n: Int :: own(x.d, 0, 0.5) && own(x.c, n, 1.0)
                          ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

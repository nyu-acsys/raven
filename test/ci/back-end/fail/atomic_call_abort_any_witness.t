  $ dune exec -- raven --shh ./atomic_call_abort_any_witness.rav
  [Error] File "./atomic_call_abort_any_witness.rav", line 29, columns 2-7:
  29 |   p(x);
         ^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./atomic_call_abort_any_witness.rav", line 28, columns 2-17:
  28 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./atomic_call_abort_any_witness.rav", line 11, columns 39-55:
  11 |   exists n: Int :: own(x.c, n, 1.0) && own(x.d, 0, 0.5)
                                              ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [Error] File "./atomic_call_abort_any_witness.rav", line 30, columns 2-15:
  30 |   fold dInv(x);
         ^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./atomic_call_abort_any_witness.rav", line 11, columns 39-55:
  11 |   exists n: Int :: own(x.c, n, 1.0) && own(x.d, 0, 0.5)
                                              ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

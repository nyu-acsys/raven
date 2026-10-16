  $ dune exec -- raven --shh ./abort_unclosable.rav
  [Error] File "./abort_unclosable.rav", line 40, columns 2-7:
  40 |   p(x);
         ^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./abort_unclosable.rav", line 39, columns 2-17:
  39 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./abort_unclosable.rav", line 18, columns 19-35:
  18 |   exists n: Int :: own(x.d, 0, 1.0) && own(x.c, n, 1.0)
                          ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

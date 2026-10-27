  $ dune exec -- raven --shh ./abort_unclosable.rav
  [Error] File "./abort_unclosable.rav", line 42, columns 2-7:
  42 |   p(x);
         ^^^^^
  Verification Error: A precondition may not hold for this call where the atomic update or invariant open around it was opened, which is where it is given up.
  [Error] File "./abort_unclosable.rav", line 41, columns 2-17:
  41 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [Error] File "./abort_unclosable.rav", line 25, columns 11-27:
  25 |   requires own(x.d, 0, 1.0)
                  ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

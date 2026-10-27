  $ dune exec -- raven --shh ./atomic_call_abort_ordinary_precondition.rav
  [Error] File "./atomic_call_abort_ordinary_precondition.rav", line 34, columns 2-7:
  34 |   p(x);
         ^^^^^
  Verification Error: A precondition may not hold for this call where the atomic update or invariant open around it was opened, which is where it is given up.
  [Error] File "./atomic_call_abort_ordinary_precondition.rav", line 33, columns 2-17:
  33 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [Error] File "./atomic_call_abort_ordinary_precondition.rav", line 17, columns 11-27:
  17 |   requires own(x.d, 0, 1.0)
                  ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

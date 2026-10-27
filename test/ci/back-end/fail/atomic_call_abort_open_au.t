  $ dune exec -- raven --shh ./atomic_call_abort_open_au.rav
  [Error] File "./atomic_call_abort_open_au.rav", line 35, columns 2-7:
  35 |   p(x);
         ^^^^^
  Verification Error: A precondition may not hold for this call where the atomic update or invariant open around it was opened, which is where it is given up.
  [Error] File "./atomic_call_abort_open_au.rav", line 33, columns 2-17:
  33 |   unfold dInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [Error] File "./atomic_call_abort_open_au.rav", line 16, columns 11-27:
  16 |   requires own(x.d, 0, 0.5)
                  ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- raven --shh ./atomic_call_abort_written_since.rav
  [Error] File "./atomic_call_abort_written_since.rav", line 20, columns 2-13:
  20 |   incr(x, z);
         ^^^^^^^^^^^
  Verification Error: The ordinary precondition of this atomic call is given up where the atomic update or invariant open around it was opened, but it depends on z, which is written since.
  [Error] File "./atomic_call_abort_written_since.rav", line 18, columns 2-17:
  18 |   unfold cInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: It was opened here.
  [1]

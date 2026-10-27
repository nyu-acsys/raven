  $ dune exec -- raven --shh ./atomic_call_abort_frame.rav
  [Error] File "./atomic_call_abort_frame.rav", line 19, columns 2-10:
  19 |   incr(x);
         ^^^^^^^^
  Verification Error: The resources held where the atomic update or invariant open around this atomic call was opened may not be restorable if the call aborts.
  [Error] File "./atomic_call_abort_frame.rav", line 17, columns 2-17:
  17 |   unfold cInv(x);
         ^^^^^^^^^^^^^^^
  Related Location: The resources held here may not be restorable if the call aborts.
  [1]

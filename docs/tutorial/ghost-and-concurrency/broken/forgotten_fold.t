  $ dune exec -- raven --shh ./forgotten_fold.rav
  [Error] File "./forgotten_fold.rav", line 26, columns 0-1:
  26 | }
       ^
  Verification Error: Missing fold for unfolded invariant evenCount(c).
  [Error] File "./forgotten_fold.rav", line 24, columns 2-21:
  24 |   unfold evenCount(c)
         ^^^^^^^^^^^^^^^^^^^
  Related Location: evenCount(c) was unfolded here.
  [1]

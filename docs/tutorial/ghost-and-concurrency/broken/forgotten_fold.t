  $ dune exec -- raven --shh ./forgotten_fold.rav
  [Error] File "./forgotten_fold.rav", line 23, columns 0-1:
  23 | }
       ^
  Verification Error: Missing fold for unfolded invariant evenCount(c).
  [Error] File "./forgotten_fold.rav", line 21, columns 2-21:
  21 |   unfold evenCount(c)
         ^^^^^^^^^^^^^^^^^^^
  Related Location: evenCount(c) was unfolded here.
  [1]

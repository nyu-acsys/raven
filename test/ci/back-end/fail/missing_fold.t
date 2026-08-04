  $ dune exec -- raven --shh ./missing_fold.rav
  [Error] File "./missing_fold.rav", line 16, columns 0-1:
  16 | }
       ^
  Error: Missing fold for unfolded invariant i(x).
  [Error] File "./missing_fold.rav", line 14, columns 2-14:
  14 |   unfold i(x);
         ^^^^^^^^^^^^
  Related Location: i(x) was unfolded here.
  [1]

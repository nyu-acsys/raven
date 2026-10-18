An invariant still open at the end of a loop body is reported there.

  $ dune exec -- raven --shh ./loop_open_invariant.rav
  [Error] File "./loop_open_invariant.rav", line 18, columns 2-3:
  18 |   }
         ^
  Verification Error: Missing fold for unfolded invariant cell(x).
  [Error] File "./loop_open_invariant.rav", line 16, columns 4-19:
  16 |     unfold cell(x);
           ^^^^^^^^^^^^^^^
  Related Location: cell(x) was unfolded here.
  [1]

  $ dune exec -- raven --shh ./projected_alias.rav
  [Error] File "./projected_alias.rav", line 15, columns 2-15:
  15 |   root_step(y);
         ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant leaf(0, 3, x), which the callee may need (the arguments identifying the two instances are not provably distinct).
  [Error] File "./projected_alias.rav", line 14, columns 2-23:
  14 |   unfold leaf(0, 3, x);
         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: leaf(0, 3, x) was unfolded here.
  [1]

  $ dune exec -- raven --shh ./sealed_alias_reentrancy.rav
  [Error] File "./sealed_alias_reentrancy.rav", line 29, columns 2-17:
  29 |   Public.step(x);
         ^^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant leaf(x).
  [Error] File "./sealed_alias_reentrancy.rav", line 28, columns 2-24:
  28 |   unfold Actual.leaf(x);
         ^^^^^^^^^^^^^^^^^^^^^^
  Related Location: leaf(x) was unfolded here.
  [1]

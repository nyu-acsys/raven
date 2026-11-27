  $ dune exec -- raven --shh ./sealed_application_reentrancy.rav
  [Error] File "./sealed_application_reentrancy.rav", line 29, columns 2-17:
  29 |   Public.step(x);
         ^^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant leaf(x).
  [Error] File "./sealed_application_reentrancy.rav", line 28, columns 2-26:
  28 |   unfold Concrete.leaf(x);
         ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: leaf(x) was unfolded here.
  [1]

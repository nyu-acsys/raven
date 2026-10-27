  $ dune exec -- raven --shh ./invariant_defined_formal_reentrancy.rav
  [Error] File "./invariant_defined_formal_reentrancy.rav", line 20, columns 4-17:
  20 |     P.consume(x);
           ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant shared(x).
  [Error] File "./invariant_defined_formal_reentrancy.rav", line 19, columns 4-28:
  19 |     unfold Actual.shared(x);
           ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: shared(x) was unfolded here.
  [1]

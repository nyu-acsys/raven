  $ dune exec -- raven --shh ./invariant_hidden_footprint.rav
  [Error] File "./invariant_hidden_footprint.rav", line 29, columns 4-17:
  29 |     P.consume(x);
           ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant cell(root).
  [Error] File "./invariant_hidden_footprint.rav", line 28, columns 4-22:
  28 |     unfold cell(root);
           ^^^^^^^^^^^^^^^^^^
  Related Location: cell(root) was unfolded here.
  [1]

  $ dune exec -- raven --shh ./invariant_required_footprint.rav
  [Error] File "./invariant_required_footprint.rav", line 33, columns 2-19:
  33 |   Applied.touch(x);
         ^^^^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant cell(root).
  [Error] File "./invariant_required_footprint.rav", line 32, columns 2-20:
  32 |   unfold cell(root);
         ^^^^^^^^^^^^^^^^^^
  Related Location: cell(root) was unfolded here.
  [1]

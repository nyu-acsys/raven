  $ dune exec -- raven --shh ./invariant_required_footprint_open.rav
  [Error] File "./invariant_required_footprint_open.rav", line 34, columns 2-19:
  34 |   Applied.touch(x);
         ^^^^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant cell(root).
  [Error] File "./invariant_required_footprint_open.rav", line 33, columns 2-20:
  33 |   unfold cell(root);
         ^^^^^^^^^^^^^^^^^^
  Related Location: cell(root) was unfolded here.
  [1]

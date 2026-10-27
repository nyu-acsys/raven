  $ dune exec -- raven --shh ./invariant_alias_mask_reentrancy.rav
  [Error] File "./invariant_alias_mask_reentrancy.rav", line 26, columns 4-17:
  26 |     P.consume(x);
           ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant cell(x).
  [Error] File "./invariant_alias_mask_reentrancy.rav", line 25, columns 4-19:
  25 |     unfold cell(x);
           ^^^^^^^^^^^^^^^
  Related Location: cell(x) was unfolded here.
  [1]

  $ dune exec -- raven --shh ./mask_reentrancy_call_prefix.rav
  [Error] File "./mask_reentrancy_call_prefix.rav", line 55, columns 2-20:
  55 |   atomic_witness(x);
         ^^^^^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant inner(x, w).
  [Error] File "./mask_reentrancy_call_prefix.rav", line 53, columns 2-21:
  53 |   unfold inner(x, w);
         ^^^^^^^^^^^^^^^^^^^
  Related Location: inner(x, w) was unfolded here.
  [1]

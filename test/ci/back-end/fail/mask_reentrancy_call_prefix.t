  $ dune exec -- raven --shh ./mask_reentrancy_call_prefix.rav
  [Error] File "./mask_reentrancy_call_prefix.rav", line 55, columns 2-20:
  55 |   atomic_witness(x);
         ^^^^^^^^^^^^^^^^^^
  Verification Error: Invariant inner is already open.
  [1]

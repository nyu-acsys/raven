  $ dune exec -- raven --shh ./mask_reentrancy_stale_args.rav
  [Error] File "./mask_reentrancy_stale_args.rav", line 22, columns 2-17:
  22 |   unfold cell(y);
         ^^^^^^^^^^^^^^^
  Verification Error: Cannot unfold cell: this instance may be the same as one already open (arguments identifying the two instances are not provably distinct).
  [1]

  $ dune exec -- raven --shh ./mask_reentrancy_nested_unfold.rav
  [Error] File "./mask_reentrancy_nested_unfold.rav", line 21, columns 2-14:
  21 |   unfold i(y);
         ^^^^^^^^^^^^
  Verification Error: Cannot unfold i: this instance may be the same as one already open (arguments identifying the two instances are not provably distinct).
  [1]

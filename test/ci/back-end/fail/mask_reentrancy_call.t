  $ dune exec -- raven --shh ./mask_reentrancy_call.rav
  [Error] File "./mask_reentrancy_call.rav", line 32, columns 2-9:
  32 |   foo(y);
         ^^^^^^^
  Verification Error: Cannot call this here: the invariant i required by the callee may be the same instance as one already open (arguments identifying the two instances are not provably distinct).
  [1]

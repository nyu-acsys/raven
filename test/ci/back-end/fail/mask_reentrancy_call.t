  $ dune exec -- raven --shh ./mask_reentrancy_call.rav
  [Error] File "./mask_reentrancy_call.rav", line 32, columns 2-9:
  32 |   foo(y);
         ^^^^^^^
  Verification Error: Missing fold for unfolded invariant i(x), which the callee may need (the arguments identifying the two instances are not provably distinct).
  [Error] File "./mask_reentrancy_call.rav", line 31, columns 2-14:
  31 |   unfold i(x);
         ^^^^^^^^^^^^
  Related Location: i(x) was unfolded here.
  [1]

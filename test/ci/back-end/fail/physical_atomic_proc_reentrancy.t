  $ dune exec -- raven --shh ./physical_atomic_proc_reentrancy.rav
  [Error] File "./physical_atomic_proc_reentrancy.rav", line 16, columns 2-16:
  16 |   inspect(other)
         ^^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant cell(c), which the callee may need (the arguments identifying the two instances are not provably distinct).
  [Error] File "./physical_atomic_proc_reentrancy.rav", line 15, columns 2-16:
  15 |   unfold cell(c)
         ^^^^^^^^^^^^^^
  Related Location: cell(c) was unfolded here.
  [1]

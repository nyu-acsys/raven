  $ dune exec -- raven --shh ./physical_atomic_proc_mask.rav
  [Error] File "./physical_atomic_proc_mask.rav", line 17, columns 2-16:
  17 |   inspect(other)
         ^^^^^^^^^^^^^^
  Verification Error: Cannot call inspect. The invariant cell required by inspect is not available in the current mask.
  [1]

  $ dune exec -- raven --shh ./atomic_call_abort_two_branches.rav
  [Error] File "./atomic_call_abort_two_branches.rav", line 22, columns 4-15:
  22 |     incr(x, z);
           ^^^^^^^^^^^
  Verification Error: Two atomic calls give up their ordinary preconditions where the same atomic update or invariant was opened; open it within each branch instead.
  [Error] File "./atomic_call_abort_two_branches.rav", line 20, columns 4-15:
  20 |     incr(x, y);
           ^^^^^^^^^^^
  Related Location: The other atomic call.
  [1]

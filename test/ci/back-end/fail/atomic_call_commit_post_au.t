  $ dune exec -- raven --shh ./atomic_call_commit_post_au.rav
  [Error] File "./atomic_call_commit_post_au.rav", line 29, columns 2-20:
  29 |   commitAU(phi, ());
         ^^^^^^^^^^^^^^^^^^
  Verification Error: An atomic postcondition may not hold at this commit point.
  [Error] File "./atomic_call_commit_post_au.rav", line 29, columns 2-20:
  29 |   commitAU(phi, ());
         ^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./atomic_call_commit_post_au.rav", line 22, columns 17-22:
  22 |   atomic ensures false
                        ^^^^^
  Related Location: This assertion may not hold.
  [1]

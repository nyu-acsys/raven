  $ dune exec -- raven --shh ./missing_commit_au.rav
  [Error] File "./missing_commit_au.rav", line 24, columns 0-1:
  24 | }
       ^
  Error: Missing fold for unfolded invariant aux(x).
  [Error] File "./missing_commit_au.rav", line 23, columns 2-16:
  23 |   unfold aux(x);
         ^^^^^^^^^^^^^^
  Related Location: aux(x) was unfolded here.
  [Error] File "./missing_commit_au.rav", line 22, columns 2-35:
  22 |   ghost var v0: Int := openAU(phi);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Missing commitAU or abortAU for open atomic update phi.
  [1]

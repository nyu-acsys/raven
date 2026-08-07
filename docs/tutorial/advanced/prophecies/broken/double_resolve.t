  $ dune exec -- raven --shh ./double_resolve.rav
  [Error] File "./double_resolve.rav", line 12, columns 2-32:
  12 |   Proph.resolve(myProph, actual)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This prophecy's resource is not available here -- it may already have been resolved, or it may still be held elsewhere in the proof.
  [Error] File "./double_resolve.rav", line 12, columns 2-32:
  12 |   Proph.resolve(myProph, actual)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- raven --shh ./outcome_grant_unchecked.rav
  [Error] File "./outcome_grant_unchecked.rav", line 33, columns 2-11:
  33 |   touch(q);
         ^^^^^^^^^
  Verification Error: An invariant region needed here is granted only in a case that may not hold.
  [1]

  $ dune exec -- raven --shh ./outcome_grant_exceptional.rav
  [Error] File "./outcome_grant_exceptional.rav", line 34, columns 4-13:
  34 |     touch(q);
           ^^^^^^^^^
  Verification Error: An invariant region needed here is granted only in a case that may not hold.
  [1]

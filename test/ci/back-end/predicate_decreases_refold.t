  $ dune exec -- raven --shh ./predicate_decreases_refold.rav
  [Error] File "./predicate_decreases_refold.rav", line 4, columns 12-19:
  4 |   decreases down(n)
                  ^^^^^^^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

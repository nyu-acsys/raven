  $ dune exec -- raven --shh ./implicit_predicate_decreases_unchanged.rav
  [Error] File "./implicit_predicate_decreases_unchanged.rav", line 7, columns 12-19:
  7 |   decreases down(n)
                  ^^^^^^^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

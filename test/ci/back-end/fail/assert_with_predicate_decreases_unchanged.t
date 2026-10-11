  $ dune exec -- raven --shh ./assert_with_predicate_decreases_unchanged.rav
  [Error] File "./assert_with_predicate_decreases_unchanged.rav", line 6, columns 12-19:
  6 |   decreases down(n)
                  ^^^^^^^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

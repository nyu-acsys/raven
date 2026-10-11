  $ dune exec -- raven --shh ./assert_with_decreases_unchanged.rav
  [Error] File "./assert_with_decreases_unchanged.rav", line 3, columns 12-13:
  3 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

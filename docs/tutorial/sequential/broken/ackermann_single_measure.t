  $ dune exec -- raven --shh ./ackermann_single_measure.rav
  [Error] File "./ackermann_single_measure.rav", line 5, columns 12-13:
  5 |   decreases m
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

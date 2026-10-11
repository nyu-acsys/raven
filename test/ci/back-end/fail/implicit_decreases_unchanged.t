  $ dune exec -- raven --shh ./implicit_decreases_unchanged.rav
  [Error] File "./implicit_decreases_unchanged.rav", line 6, columns 12-13:
  6 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

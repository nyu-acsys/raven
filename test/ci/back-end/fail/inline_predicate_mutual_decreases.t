  $ dune exec -- raven --shh ./inline_predicate_mutual_decreases.rav
  [Error] File "./inline_predicate_mutual_decreases.rav", line 4, columns 12-13:
  4 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [Error] File "./inline_predicate_mutual_decreases.rav", line 10, columns 12-13:
  10 |   decreases n
                   ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

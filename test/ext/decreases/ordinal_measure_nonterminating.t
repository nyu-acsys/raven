  $ dune exec -- raven --shh ./ordinal_measure_nonterminating.rav
  [Error] File "./ordinal_measure_nonterminating.rav", line 6, columns 12-13:
  6 |   decreases o
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

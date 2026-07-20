  $ dune exec -- raven --shh ./fac_nonterminating.rav
  [Error] File "./fac_nonterminating.rav", line 5, columns 12-13:
  5 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

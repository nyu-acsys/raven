  $ dune exec -- raven --shh ./fac_nonterminating.rav
  [Error] File "./fac_nonterminating.rav", line 4, columns 12-13:
  4 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

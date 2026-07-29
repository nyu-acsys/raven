  $ dune exec -- raven --shh ./mutual_nonterminating.rav
  [Error] File "./mutual_nonterminating.rav", line 2, columns 12-13:
  2 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

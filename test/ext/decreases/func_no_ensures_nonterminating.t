  $ dune exec -- raven --shh ./func_no_ensures_nonterminating.rav
  [Error] File "./func_no_ensures_nonterminating.rav", line 6, columns 12-13:
  6 |   decreases n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

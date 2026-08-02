  $ dune exec -- raven --shh ./lexicographic_nonterminating.rav
  [Error] File "./lexicographic_nonterminating.rav", line 3, columns 12-13:
  3 |   decreases m, n
                  ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

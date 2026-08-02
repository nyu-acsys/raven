  $ dune exec -- raven --shh ./auto_order_adt_nonterminating.rav
  [Error] File "./auto_order_adt_nonterminating.rav", line 11, columns 14-16:
  11 |     decreases ls
                     ^^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

  $ dune exec -- raven --shh ./auto_order_adt_no_recursive_field.rav
  [Error] File "./auto_order_adt_no_recursive_field.rav", line 13, columns 14-15:
  13 |     decreases c
                     ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

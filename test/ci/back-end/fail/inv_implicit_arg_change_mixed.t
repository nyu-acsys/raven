  $ dune exec -- raven --shh ./inv_implicit_arg_change_mixed.rav
  [Error] File "./inv_implicit_arg_change_mixed.rav", line 16, columns 2-12:
  16 |   fold i(x);
         ^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./inv_implicit_arg_change_mixed.rav", line 16, columns 2-12:
  16 |   fold i(x);
         ^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

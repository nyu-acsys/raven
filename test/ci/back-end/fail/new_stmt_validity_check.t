  $ dune exec -- raven --shh new_stmt_validity_check.rav
  [Error] File "new_stmt_validity_check.rav", line 7, columns 4-37:
  7 |     l := new(f: Agree_Int.agree_top);
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not prove validity of initially-allocated value.
  [1]

  $ dune exec -- ../../../../bin/raven.exe --shh ./missing_permissions.rav
  [Error] File "./missing_permissions.rav", line 16, columns 3-3:
  16 |   }
          ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./missing_permissions.rav", line 13, columns 12-45:
  13 |     ensures exists v:Int :: own(x, f, v, 1.0)
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This is the postcondition that may not hold.
  [1]

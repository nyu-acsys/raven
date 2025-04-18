  $ dune exec -- raven --shh ./missing_permissions.rav
  [Error] File "./missing_permissions.rav", line 16, columns 3-3:
  16 |   }
          ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./missing_permissions.rav", line 13, columns 28-44:
  13 |     ensures exists v:Int :: own(x.f, v, 1.0)
                                   ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./missing_permissions.rav
  [Error] File "./missing_permissions.rav", line 13, columns 12-45:
  13 |     ensures exists v:Int :: own(x, f, v, 1.0)
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not exhale stmt.
  [1]

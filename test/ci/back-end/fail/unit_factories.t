  $ dune exec -- raven --shh ./unit_factories.rav
  [Error] File "./unit_factories.rav", line 11, columns 1-1:
  11 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./unit_factories.rav", line 9, columns 10-28:
  9 |   ensures own(x.B.f, n, 1.0)
                ^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- raven --shh ./instance_inline_predicates_fail.rav
  [Error] File "./instance_inline_predicates_fail.rav", line 30, columns 1-1:
  30 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./instance_inline_predicates_fail.rav", line 27, columns 10-30:
  27 |   ensures own(x.value, 4, 1.0)
                 ^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

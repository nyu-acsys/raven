  $ dune exec -- raven --shh ./sealed_functor_alias_resource.rav
  [Error] File "./sealed_functor_alias_resource.rav", line 9, columns 3-3:
  9 | { }
         ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sealed_functor_alias_resource.rav", line 8, columns 10-35:
  8 |   ensures own(x.View.value, 0, 1.0)
                ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

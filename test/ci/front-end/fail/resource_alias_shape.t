  $ dune exec -- raven --shh ./resource_alias_shape.rav
  [Error] File "./resource_alias_shape.rav", line 2, columns 18-22:
  2 | module Bad { pred cell(x: Ref, v: Int) = cell }
                        ^^^^
  Type Error: A resource alias must preserve the target's parameter shape.
  [1]

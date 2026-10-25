  $ dune exec -- raven --shh ./resource_alias_modes.rav
  [Error] File "./resource_alias_modes.rav", line 2, columns 18-22:
  2 | module Bad { pred cell(x: Int) = cell }
                        ^^^^
  Type Error: A resource alias must preserve the target's parameter types and modes.
  [1]

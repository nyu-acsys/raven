  $ dune exec -- raven --shh ./resource_alias_kind.rav
  [Error] File "./resource_alias_kind.rav", line 2, columns 18-24:
  2 | module Bad { pred shared(x: Ref) = shared }
                        ^^^^^^
  Type Error: A resource alias must name a resource of the same kind.
  [1]

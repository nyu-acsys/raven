  $ dune exec -- raven --shh ./forwarding_namespace_outputs.rav
  [Error] File "./forwarding_namespace_outputs.rav", line 46, columns 7-14:
  46 | module Applied = Client[Actual]
              ^^^^^^^
  Type Error: Incompatible module namespace contracts: the granted mask of pop is weaker than promised.
  [1]

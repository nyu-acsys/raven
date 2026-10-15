  $ dune exec -- raven --shh ./generative_instances.rav
  [Error] File "./generative_instances.rav", line 10, columns 9-10:
  10 |     b := a;
                ^
  Type Error: Expected an expression of type
    B.U
  but found an expression of type
    A.U.
  
  B.U and A.U come from two separate instantiations of F with the same arguments. Module instantiation is generative: each instantiation site produces its own distinct type, even when the arguments are identical. Bind a single instantiation explicitly and reuse it from both places, e.g. `module Shared = F[...]`.
  [1]

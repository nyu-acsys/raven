  $ dune exec -- raven --shh ./forwarding_namespace_outputs.rav
  [Error] File "./forwarding_namespace_outputs.rav", line 15, columns 43-56:
  15 |  pred stack(x: Ref) returns(implicit ghost xs: List[A.T]) { N.stack(x, List.nil) }
                                                  ^^^^^^^^^^^^^
  Verification Error: Two instances held at the same time that agree on the explicit parameters may disagree on this implicit parameter.
  [Error] File "./forwarding_namespace_outputs.rav", line 15, columns 60-80:
  15 |  pred stack(x: Ref) returns(implicit ghost xs: List[A.T]) { N.stack(x, List.nil) }
                                                                   ^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ dune exec -- raven --shh ./sealed_hidden_member_implicit.rav
  [Error] File "./sealed_hidden_member_implicit.rav", line 30, columns 23-27:
  30 |     var t := ListStack.cons(1, s);
                              ^^^^
  Error: cons is not accessible here: ListStack is a sealed module, which exposes only the members of interface Stack.
  [1]

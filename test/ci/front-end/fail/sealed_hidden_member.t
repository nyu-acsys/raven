  $ dune exec -- raven --shh ./sealed_hidden_member.rav
  [Error] File "./sealed_hidden_member.rav", line 32, columns 20-23:
  32 |     assert S.size(S.nil) == 0;
                           ^^^
  Error: nil is not accessible here: S is an instance of the sealed module ListStack, which exposes only the members of interface Stack.
  [1]

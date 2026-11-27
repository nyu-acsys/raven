Copies of quantified predicates retain independent witnesses and lexical shadowing.

  $ raven --shh inline_bound_scopes.rav
  Verification successful.

An inlined existential cannot capture an unrelated caller variable.

  $ raven --shh fail/inline_bound_scopes.rav > failure.out 2>&1
  [1]
  $ grep -c 'Verification Error:' failure.out
  1
  $ grep -qi timeout failure.out
  [1]

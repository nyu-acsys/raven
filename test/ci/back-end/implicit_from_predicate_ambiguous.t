  $ dune exec -- raven --shh ./implicit_from_predicate_ambiguous.rav
  [Error] File "./implicit_from_predicate_ambiguous.rav", line 15, columns 4-14:
  15 |     C.call(e);
           ^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "./implicit_from_predicate_ambiguous.rav", line 15, columns 4-14:
  15 |     C.call(e);
           ^^^^^^^^^^
  Related Location: No witness could be computed for $bind_n&1, so it was treated as an arbitrary value.
  [Error] File "./implicit_from_predicate_ambiguous.rav", line 7, columns 13-23:
  7 |     requires step(e, n)
                   ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

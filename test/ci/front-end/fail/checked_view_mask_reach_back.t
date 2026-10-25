  $ dune exec -- raven --shh ./checked_view_mask_reach_back.rav
  [Error] File "./checked_view_mask_reach_back.rav", line 3, columns 7-15:
  3 |   pred resource(x: Ref) { shared(x) }
             ^^^^^^^^
  Type Error: predicate resource implements interface Required's abstract resource, but its definition depends on Actual.shared, which Required also declares.
  [1]

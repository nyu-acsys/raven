  $ dune exec -- raven --shh ./heap_fusion_reverse_consumed.rav
  [Error] File "./heap_fusion_reverse_consumed.rav", line 6, columns 9-25:
  6 |   exhale own(x.f, 7, 0.5);
               ^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_reverse_consumed.rav", line 6, columns 9-25:
  6 |   exhale own(x.f, 7, 0.5);
               ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

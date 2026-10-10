  $ dune exec -- raven --shh ./heap_fusion_same_chunk.rav
  [Error] File "./heap_fusion_same_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_same_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh --no-heap-fusion ./heap_fusion_same_chunk.rav
  [Error] File "./heap_fusion_same_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_same_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_changed_chunk.rav
  [Error] File "./heap_fusion_changed_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_changed_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh --no-heap-fusion ./heap_fusion_changed_chunk.rav
  [Error] File "./heap_fusion_changed_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_changed_chunk.rav", line 5, columns 9-26:
  5 |   exhale own(x.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_predicate.rav
  [Error] File "./heap_fusion_predicate.rav", line 4, columns 9-17:
  4 |   exhale token(x);
               ^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_predicate.rav", line 4, columns 9-17:
  4 |   exhale token(x);
               ^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
  $ dune exec -- raven --shh --no-heap-fusion ./heap_fusion_predicate.rav
  [Error] File "./heap_fusion_predicate.rav", line 4, columns 9-17:
  4 |   exhale token(x);
               ^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_predicate.rav", line 4, columns 9-17:
  4 |   exhale token(x);
               ^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_duplicate.rav
  [Error] File "./heap_fusion_duplicate.rav", line 6, columns 9-47:
  6 |   exhale own(x.f, 1, 0.75) && own(y.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_duplicate.rav", line 6, columns 30-47:
  6 |   exhale own(x.f, 1, 0.75) && own(y.f, 1, 0.75);
                                    ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh --no-heap-fusion ./heap_fusion_duplicate.rav
  [Error] File "./heap_fusion_duplicate.rav", line 6, columns 9-47:
  6 |   exhale own(x.f, 1, 0.75) && own(y.f, 1, 0.75);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_duplicate.rav", line 6, columns 30-47:
  6 |   exhale own(x.f, 1, 0.75) && own(y.f, 1, 0.75);
                                    ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

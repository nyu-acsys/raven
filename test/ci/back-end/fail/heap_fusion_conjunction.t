  $ dune exec -- raven --shh ./heap_fusion_conjunction_permissions.rav
  [Error] File "./heap_fusion_conjunction_permissions.rav", line 6, columns 9-47:
  6 |   exhale own(x.f, 7, 0.75) && own(y.f, 7, 0.75);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_conjunction_permissions.rav", line 6, columns 30-47:
  6 |   exhale own(x.f, 7, 0.75) && own(y.f, 7, 0.75);
                                    ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_conjunction_pure.rav
  [Error] File "./heap_fusion_conjunction_pure.rav", line 6, columns 9-52:
  6 |   exhale own(x.f, 7, 0.25) && b && own(x.f, 7, 0.25);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_conjunction_pure.rav", line 6, columns 30-31:
  6 |   exhale own(x.f, 7, 0.25) && b && own(x.f, 7, 0.25);
                                    ^
  Related Location: This assertion may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_conjunction_guard.rav
  [Error] File "./heap_fusion_conjunction_guard.rav", line 6, columns 9-61:
  6 |   exhale (b ==> own(x.f, 7, 0.5)) && (c ==> own(x.f, 7, 0.5));
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_conjunction_guard.rav", line 6, columns 44-60:
  6 |   exhale (b ==> own(x.f, 7, 0.5)) && (c ==> own(x.f, 7, 0.5));
                                                  ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_conjunction_count.rav
  [Error] File "./heap_fusion_conjunction_count.rav", line 6, columns 9-33:
  6 |   exhale counted(x) && counted(x);
               ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_conjunction_count.rav", line 6, columns 23-33:
  6 |   exhale counted(x) && counted(x);
                             ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
  $ dune exec -- raven --shh ./heap_fusion_conjunction_value.rav
  [Error] File "./heap_fusion_conjunction_value.rav", line 6, columns 9-37:
  6 |   exhale valued(x, 7) && valued(x, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./heap_fusion_conjunction_value.rav", line 6, columns 25-37:
  6 |   exhale valued(x, 7) && valued(x, 7);
                               ^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

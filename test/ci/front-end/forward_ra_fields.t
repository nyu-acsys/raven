  $ dune exec -- raven --shh --typeonly ./forward_ra_fields.rav
  Verification successful.
  $ dune exec -- raven --shh ./forward_ra_fields.rav
  Verification successful.
  $ dune exec -- raven --shh --typeonly ./fail/forward_ra_fraction.rav
  [Error] File "./fail/forward_ra_fraction.rav", line 4, columns 52-55:
  4 | pred root_before(r: Ref) { own(r.before, RootRA.id, 0.5) }
                                                          ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [Error] File "./fail/forward_ra_fraction.rav", line 5, columns 50-53:
  5 | pred root_after(r: Ref) { own(r.after, RootRA.id, 0.5) }
                                                        ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [Error] File "./fail/forward_ra_fraction.rav", line 6, columns 56-59:
  6 | pred root_explicit(r: Ref) { own(r.explicit, RootRA.id, 0.5) }
                                                              ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [Error] File "./fail/forward_ra_fraction.rav", line 12, columns 52-55:
  12 |   pred nested_before(r: Ref) { own(r.before, RA.id, 0.5) }
                                                           ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [Error] File "./fail/forward_ra_fraction.rav", line 13, columns 50-53:
  13 |   pred nested_after(r: Ref) { own(r.after, RA.id, 0.5) }
                                                         ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [Error] File "./fail/forward_ra_fraction.rav", line 14, columns 56-59:
  14 |   pred nested_explicit(r: Ref) { own(r.explicit, RA.id, 0.5) }
                                                               ^^^
  Type Error: 'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument.
  [1]
  $ dune exec -- raven --shh --typeonly ./fail/forward_ra_write.rav
  [Error] File "./fail/forward_ra_write.rav", line 4, columns 28-50:
  4 | lemma root_before(r: Ref) { r.before := RootRA.id; }
                                  ^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field before, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [Error] File "./fail/forward_ra_write.rav", line 5, columns 27-48:
  5 | lemma root_after(r: Ref) { r.after := RootRA.id; }
                                 ^^^^^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field after, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [Error] File "./fail/forward_ra_write.rav", line 6, columns 30-54:
  6 | lemma root_explicit(r: Ref) { r.explicit := RootRA.id; }
                                    ^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field explicit, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [Error] File "./fail/forward_ra_write.rav", line 12, columns 32-50:
  12 |   lemma nested_before(r: Ref) { r.before := RA.id; }
                                       ^^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field before, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [Error] File "./fail/forward_ra_write.rav", line 13, columns 31-48:
  13 |   lemma nested_after(r: Ref) { r.after := RA.id; }
                                      ^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field after, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [Error] File "./fail/forward_ra_write.rav", line 14, columns 34-54:
  14 |   lemma nested_explicit(r: Ref) { r.explicit := RA.id; }
                                         ^^^^^^^^^^^^^^^^^^^^
  Type Error: Cannot assign directly to field explicit, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead.
  [1]

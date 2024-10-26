  $ dune exec -- raven --shh ./treiber_stack_atomics.rav
  [Warning] File "./treiber_stack_atomics.rav", line 20, columns 21-134:
  20 |       (xs != nil && (exists tl0: Ref, q: Real ::  q > 0.0 && (own(x, value, xs.head, q) && own(x, next, tl0, q) && list(tl0, xs.tail))))
                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: No witnesses could be computed for: q.
  Verification successful.

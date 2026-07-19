  $ dune exec -- raven --shh ./treiber_stack_atomics.rav
  [Warning] File "./treiber_stack_atomics.rav", line 18, columns 20-135:
  18 |     (xs != nil() && (exists tl0: Ref, q:Real ::  q > 0.0 && (own(hd.value, xs.elem, q) && own(hd.next, tl0, q) && is_list(tl0, xs.tl))))
                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  No witness could be computed for `q` -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  Verification successful.

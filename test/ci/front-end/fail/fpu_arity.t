  $ dune exec -- raven --shh ./fpu_location_arity.rav
  [Error] File "./fpu_location_arity.rav", line 4, columns 2-20:
  4 |   fpu(x.f, 1, 2, 3);
        ^^^^^^^^^^^^^^^^^^
  Type Error: fpu expects a field location followed by one or two values, or a reference and field followed by one or two values.
  [1]

  $ dune exec -- raven --shh ./fpu_reference_arity.rav
  [Error] File "./fpu_reference_arity.rav", line 4, columns 2-21:
  4 |   fpu(x, f, 1, 2, 3);
        ^^^^^^^^^^^^^^^^^^^
  Type Error: fpu expects a field location followed by one or two values, or a reference and field followed by one or two values.
  [1]

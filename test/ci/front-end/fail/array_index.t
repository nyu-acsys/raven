  $ dune exec -- raven --shh ./array_index_expr.rav
  [Error] File "./array_index_expr.rav", line 8, columns 8-11:
  8 |   x := a[0] + 1;
              ^^^
  Type Error: An array entry can only be read by an assignment `x := a[i]`, or named as a location, as in `own(a[i], v)`.
  [1]
  $ dune exec -- raven --shh ./array_index_spec.rav
  [Error] File "./array_index_spec.rav", line 8, columns 10-13:
  8 |   assert a[0] == 1;
                ^^^
  Type Error: An array entry can only be read by an assignment `x := a[i]`, or named as a location, as in `own(a[i], v)`.
  [1]
  $ dune exec -- raven --shh ./array_index_update.rav
  [Error] File "./array_index_update.rav", line 7, columns 2-17:
  7 |   b := a[0 := 1];
        ^^^^^^^^^^^^^^^
  Type Error: An array is not a value. To change an entry, assign to it with `a[i] := v`.
  [1]
  $ dune exec -- raven --shh ./array_index_two_lhs.rav
  [Error] File "./array_index_two_lhs.rav", line 7, columns 2-15:
  7 |   x, y := a[0];
        ^^^^^^^^^^^^^
  Type Error: An array entry can only be read into a single variable.
  [1]
  $ dune exec -- raven --shh ./array_index_ghost.rav
  [Error] File "./array_index_ghost.rav", line 8, columns 5-15:
  8 |   {! a[0] := 2; !}
           ^^^^^^^^^^
  Type Error: Cannot assign to non-ghost field A.value in ghost context.
  [1]
  $ dune exec -- raven --shh ./array_index_type.rav
  [Error] File "./array_index_type.rav", line 7, columns 9-13:
  7 |   x := a[true];
               ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [1]
  $ dune exec -- raven --shh ./array_index_call_arg.rav
  [Error] File "./array_index_call_arg.rav", line 7, columns 5-8:
  7 |   q(a[0]);
           ^^^
  Type Error: An array entry can only be read by an assignment `x := a[i]`, or named as a location, as in `own(a[i], v)`.
  [1]

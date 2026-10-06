  $ dune exec -- raven --shh ./map_index_assign_const.rav
  [Error] File "./map_index_assign_const.rav", line 4, columns 2-3:
  4 |   m[0] := 1;
        ^
  Type Error: Cannot assign to value m.
  [1]
  $ dune exec -- raven --shh ./index_assign_non_map.rav
  [Error] File "./index_assign_non_map.rav", line 4, columns 2-3:
  4 |   x[0] := 1;
        ^
  Type Error: Expected an expression of type
    Map[Bot, Any]
  but found an expression of type
    Int.
  [1]
  $ dune exec -- raven --shh ./index_assign_field.rav
  [Error] File "./index_assign_field.rav", line 7, columns 2-5:
  7 |   x.f[0] := 1;
        ^^^
  Syntax Error: Expected a variable, possibly indexed, on the left-hand side of an indexed assignment.
  [1]

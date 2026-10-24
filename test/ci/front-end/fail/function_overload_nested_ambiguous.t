  $ dune exec -- raven --shh --typeonly ./function_overload_nested_ambiguous.rav
  [Error] File "./function_overload_nested_ambiguous.rav", line 13, columns 9-15:
  13 |   assert get(b) == 1;
                ^^^^^^
  Type Error: Ambiguous function name get (2 candidates); add a type annotation or qualify the call.
  [1]

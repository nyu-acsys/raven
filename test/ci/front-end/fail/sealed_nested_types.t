  $ dune exec -- raven --shh --typeonly ./sealed_nested_types.rav
  [Error] File "./sealed_nested_types.rav", line 9, columns 7-10:
  9 |   func get(b: Box[E]) returns (r: E) { b.value }
             ^^^
  Type Error: Formal parameter b of function get does not match parameter b of get in interface DeepSpec.
  [Error] File "./sealed_nested_types.rav", line 16, columns 7-10:
  16 |   func get(b: Box[Box[Bool]]) returns (r: Int) { 0 }
              ^^^
  Type Error: Formal parameter b of function get does not match parameter b of get in interface IntSpec.
  [Error] File "./sealed_nested_types.rav", line 24, columns 7-10:
  24 |   func get(b: Box[Box[Int]]) returns (r: Int) { b.value.value }
              ^^^
  Type Error: Formal parameter b of function get does not match parameter b of get in interface NamedElementSpec.
  [Error] File "./sealed_nested_types.rav", line 32, columns 7-10:
  32 |   func get(b: Box[Box[Int]]) returns (r: Int) { b.value.value }
              ^^^
  Type Error: Formal parameter b of function get does not match parameter b of get in interface NamedBoxSpec.
  [1]

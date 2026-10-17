Every member that fails to type-check is reported, but not the uses of a failed member:

  $ dune exec -- raven --shh ./multiple_errors.rav
  [Error] File "./multiple_errors.rav", line 4, columns 17-22:
  4 |   var b: Bool := x + 1;
                       ^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [Error] File "./multiple_errors.rav", line 7, columns 22-32:
  7 | func bad_signature(x: NoSuchType) returns (r: Int)
                            ^^^^^^^^^^
  Error: Unknown identifier NoSuchType.
  [Error] File "./multiple_errors.rav", line 14, columns 15-19:
  14 |   val c: Int = true
                      ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [Error] File "./multiple_errors.rav", line 22, columns 11-26:
  22 | module N : NoSuchInterface {
                  ^^^^^^^^^^^^^^^
  Error: Unknown identifier NoSuchInterface.
  [Error] File "./multiple_errors.rav", line 31, columns 9-10:
  31 |   assert 1;
                ^
  Type Error: Expected an expression of type
    Perm
  but found an expression of type
    Int.
  [1]

With --max-errors, type checking stops once there are more errors than the limit:

  $ dune exec -- raven --shh --max-errors=2 ./multiple_errors.rav
  [Error] File "./multiple_errors.rav", line 4, columns 17-22:
  4 |   var b: Bool := x + 1;
                       ^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [Error] File "./multiple_errors.rav", line 7, columns 22-32:
  7 | func bad_signature(x: NoSuchType) returns (r: Int)
                            ^^^^^^^^^^
  Error: Unknown identifier NoSuchType.
  [Error] Error: Stopped after 2 errors; use --max-errors to change the limit
  [1]

  $ dune exec -- raven --shh ./assignment_proc_narrowing.rav
  [Error] File "./assignment_proc_narrowing.rav", line 9, columns 2-3:
  9 |   r := fraction();
        ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Real.
  [1]

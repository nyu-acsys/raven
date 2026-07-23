  $ dune exec -- raven --shh ./type_annot_mismatch.rav
  [Error] File "./type_annot_mismatch.rav", line 3, columns 15-16:
  3 | val x: Bool = (3 : Int)
                     ^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [1]

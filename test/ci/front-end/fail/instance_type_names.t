  $ dune exec -- raven --shh ./instance_type_names.rav
  [Error] File "./instance_type_names.rav", line 4, columns 27-28:
  4 |   var t: Seq[Seq[Bool]] := s;
                                 ^
  Type Error: Expected an expression of type
    Library.Seq[Library.Seq[Bool]]
  but found an expression of type
    Library.Seq[Library.Seq[Int]].
  [1]

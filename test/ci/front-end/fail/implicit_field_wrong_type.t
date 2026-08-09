  $ dune exec -- raven --shh ./implicit_field_wrong_type.rav
  [Error] File "./implicit_field_wrong_type.rav", line 24, columns 4-16:
  24 |   { incr(x.bit); }
           ^^^^^^^^^^^^
  Type Error: Field f stands for Client.bit, of type Fld[Bool], but interface IntField declares it with type Fld[Int].
  [1]

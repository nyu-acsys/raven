  $ dune exec -- raven --shh ./map_literal_key_type.rav
  [Error] File "./map_literal_key_type.rav", line 3, columns 13-21:
  3 |     var m := {else 4}
                   ^^^^^^^^
  Type Error: Cannot infer the key type of this map literal; annotate it, as in `({else 0} : Map[Int, Int])`.
  [1]

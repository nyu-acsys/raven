  $ dune exec -- raven --shh ./atomics_not_word_sized.rav
  [Error] File "./atomics_not_word_sized.rav", line 19, columns 4-26:
  19 |   { b := cas(x.big, m, m); }
           ^^^^^^^^^^^^^^^^^^^^^^
  Type Error: `Map[Int, Int]` is not word-sized, so it cannot implement Library.WordSized. An atomic primitive operates on a single machine word: Int, Bool, Ref, or a data type with at most four constructors each taking at most one of those.
  [1]

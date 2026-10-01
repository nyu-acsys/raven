  $ dune exec -- raven --shh ./lclist_buggy.rav
  [Error] File "./lclist_buggy.rav", line 145, columns 16-57:
  145 |                 fold resource((p, vp))[nx := n, vx := k];
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./lclist_buggy.rav", line 20, columns 16-35:
  20 |                 own((r#0).next, nx) 
                       ^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

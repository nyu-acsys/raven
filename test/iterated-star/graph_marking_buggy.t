  $ dune exec -- raven --shh ./graph_marking_buggy.rav
  [Error] File "./graph_marking_buggy.rav", line 111, columns 8-48:
  111 | 	assert forall n: Ref :: n in nodes ==> mMap2[n];
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]

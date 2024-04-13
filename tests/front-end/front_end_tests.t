
  $ dune exec -- ../../bin/raven.exe --shh ./data_type.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./datatype_test.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./exhale_existential_qual_pred_elim.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./exhale_existential_quant_elim.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./field_type_test.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./inhale_exhale.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./loop-rewriter_test.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./map_compr.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./own_expr_rewriter_test.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./parametric_frac.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./predicates.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./tuple.rav
  Verification successful.

  $ dune exec -- ../../bin/raven.exe --shh ./simple.rav
  [Error] File "./simple.rav", line 9, columns 10-16:
  9 |   ensures x == 5
                ^^^^^^
  SMT Error: Assertion is not valid
  [1]


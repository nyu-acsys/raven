  $ dune exec -- raven --shh ./sealed_module_hidden_definition.rav
  [Error] File "./sealed_module_hidden_definition.rav", line 13, columns 44-44:
  13 | lemma l() ensures S.inc(S.zero) != S.zero {}
                                                   ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sealed_module_hidden_definition.rav", line 13, columns 18-41:
  13 | lemma l() ensures S.inc(S.zero) != S.zero {}
                         ^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ dune exec -- raven --shh ./inherited_contract_partial.rav
  [Error] File "./inherited_contract_partial.rav", line 16, columns 8-14:
  16 |   lemma get_mk(y: A) ensures true {}
               ^^^^^^
  Type Error: lemma get_mk does not have the same postcondition as get_mk in interface Box. Repeat its contract exactly, or omit it to inherit it.
  [1]

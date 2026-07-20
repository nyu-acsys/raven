  $ dune exec -- raven --shh ./loop_nonterminating.rav
  [Error] File "./loop_nonterminating.rav", line 7, columns 14-15:
  7 |     decreases i
                    ^
  Verification Error: This loop may not terminate: its decreases clause's termination measure may not decrease on every iteration.
  [1]

  $ dune exec -- raven --shh ./return_proc.rav
  [Error] File "./return_proc.rav", line 11, columns 11-14:
  11 |     return p();
                  ^^^
  Type Error: Procedure p can only be called as the right-hand side of an assignment statement, e.g. `x := p(...)`. Assign its result to a variable first if you need to use it in an expression.
  [1]

  $ dune exec -- raven --shh ./auto_pred.rav
  [Error] File "./auto_pred.rav", line 4, columns 0-4:
  4 | auto pred p(x: Ref) {
      ^^^^
  Syntax Error: `auto` applies only to lemmas and axioms. To have a predicate or function replaced by its body where it is used, declare it `inline`.
  [1]
  $ dune exec -- raven --shh ./auto_func.rav
  [Error] File "./auto_func.rav", line 2, columns 0-4:
  2 | auto func f(x: Int) returns (r: Int) {
      ^^^^
  Syntax Error: `auto` applies only to lemmas and axioms. To have a predicate or function replaced by its body where it is used, declare it `inline`.
  [1]
  $ dune exec -- raven --shh ./inline_inv.rav
  [Error] File "./inline_inv.rav", line 4, columns 7-10:
  4 | inline inv i(x: Ref) {
             ^^^
  Syntax Error: An invariant cannot be inline.
  [1]
  $ dune exec -- raven --shh ./inline_pred_recursive.rav
  [Error] File "./inline_pred_recursive.rav", line 5, columns 57-64:
  5 |   x == null ? true : (exists y: Ref :: own(x.next, y) && list(y))
                                                               ^^^^^^^
  Type Error: Inline predicate list cannot be recursive.
  [1]

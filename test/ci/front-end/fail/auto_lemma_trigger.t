  $ dune exec -- raven --shh ./auto_lemma_trigger_not_auto.rav
  [Error] File "./auto_lemma_trigger_not_auto.rav", line 5, columns 11-15:
  5 |   ensures {f(n)} f(n) == f(n)
                 ^^^^
  Type Error: Only the postcondition of an auto lemma can have triggers.
  [1]
  $ dune exec -- raven --shh ./auto_lemma_trigger_proc.rav
  [Error] File "./auto_lemma_trigger_proc.rav", line 5, columns 11-15:
  5 |   ensures {f(n)} f(n) == f(n)
                 ^^^^
  Type Error: Only the postcondition of an auto lemma can have triggers.
  [1]
  $ dune exec -- raven --shh ./auto_lemma_trigger_param.rav
  [Error] File "./auto_lemma_trigger_param.rav", line 5, columns 11-15:
  5 |   ensures {f(n)} f(n) == f(m) ==> n == n
                 ^^^^
  Type Error: This trigger does not mention the parameter m.
  [1]

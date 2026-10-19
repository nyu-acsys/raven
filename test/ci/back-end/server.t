A server answers each request with what a run with the same arguments would output,
whatever it ran before.

  $ req() { printf '{"id":%s,"cwd":"%s","args":[%s]}\n' "$1" "${3:-$PWD}" "$2"; }
  $ { req 1 '"--shh","agree_inhale.rav"'
  >   req 2 '"--shh","fail/fpu_fail.rav"'
  >   req 3 '"--shh","--typeonly","agree_inhale.rav"'
  >   req 4 '"--shh","fail/fpu_fail.rav"'
  >   echo 'not a request'
  >   req 5 '"--shh","agree_inhale.rav"' /no/such/directory
  > } | dune exec -- raven --server > answers
  $ cat answers
  {"id":1,"exit":0,"stdout":"Verification successful.\n","stderr":""}
  {"id":2,"exit":1,"stdout":"","stderr":"[Error] File \"fail/fpu_fail.rav\", line 7, columns 2-14:\n7 |   fpu(x.f, 4);\n      ^^^^^^^^^^^^\nVerification Error: This update may not be frame-preserving.\n"}
  {"id":3,"exit":0,"stdout":"Verification successful.\n","stderr":""}
  {"id":4,"exit":1,"stdout":"","stderr":"[Error] File \"fail/fpu_fail.rav\", line 7, columns 2-14:\n7 |   fpu(x.f, 4);\n      ^^^^^^^^^^^^\nVerification Error: This update may not be frame-preserving.\n"}
  {"id":null,"error":"Not a request: not a request"}
  {"id":5,"error":"No such directory: /no/such/directory"}

The same request gets the same answer, also after others.

  $ sed -n 2p answers | sed 's/"id":2/"id":4/' > second
  $ sed -n 4p answers | cmp - second && echo identical
  identical

A cancelled run is answered as such, and the server goes on with the next request. A
cancellation of a run that is done is ignored.

  $ { req 6 '"--shh","agree_inhale.rav"'
  >   echo '{"cancel":6}'
  >   echo '{"cancel":1}'
  >   req 7 '"--shh","agree_inhale.rav"'
  > } | dune exec -- raven --server
  {"id":6,"cancelled":true}
  {"id":7,"exit":0,"stdout":"Verification successful.\n","stderr":""}

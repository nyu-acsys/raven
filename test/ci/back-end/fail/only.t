--only verifies a single member, module or named assertion and assumes the rest.

  $ dune exec -- raven --shh ./only.rav
  [Error] File "./only.rav", line 6, columns 16-21:
  6 |   assert wrong: x > 5;
                      ^^^^^
  Verification Error: Assertion 'wrong': This assertion may be violated.
  [Error] File "./only.rav", line 12, columns 23-29:
  12 |     assert loop_wrong: i >= 1;
                              ^^^^^^
  Verification Error: Assertion 'loop_wrong': This assertion may be violated.
  [Error] File "./only.rav", line 25, columns 4-4:
  25 |   {}
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./only.rav", line 24, columns 12-22:
  24 |     ensures x + 1 == x
                   ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./only.rav", line 35, columns 27-33:
  35 |     invariant wrong_entry: i >= 1
                                  ^^^^^^
  Verification Error: Assertion 'wrong_entry': This loop invariant may not hold upon loop entry.
  [Error] File "./only.rav", line 35, columns 27-33:
  35 |     invariant wrong_entry: i >= 1
                                  ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./only.rav", line 36, columns 26-32:
  36 |     invariant wrong_step: i <= 1
                                 ^^^^^^
  Verification Error: Assertion 'wrong_step': This loop invariant may not be maintained.
  [Error] File "./only.rav", line 36, columns 26-32:
  36 |     invariant wrong_step: i <= 1
                                 ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./only.rav", line 48, columns 16-21:
  48 |   assert wrong: x > 5 with {
                       ^^^^^
  Verification Error: Assertion 'wrong': This assertion may be violated.
  [1]
  $ dune exec -- raven --shh --only M.fine ./only.rav
  Verification successful.
  $ dune exec -- raven --shh --only M ./only.rav
  [Error] File "./only.rav", line 25, columns 4-4:
  25 |   {}
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./only.rav", line 24, columns 12-22:
  24 |     ensures x + 1 == x
                   ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
  $ dune exec -- raven --shh --only p ./only.rav
  [Error] File "./only.rav", line 6, columns 16-21:
  6 |   assert wrong: x > 5;
                      ^^^^^
  Verification Error: Assertion 'wrong': This assertion may be violated.
  [Error] File "./only.rav", line 12, columns 23-29:
  12 |     assert loop_wrong: i >= 1;
                              ^^^^^^
  Verification Error: Assertion 'loop_wrong': This assertion may be violated.
  [1]

Only the named assertion is checked, including one in a loop.

  $ dune exec -- raven --shh --only p.positive ./only.rav
  Verification successful.
  $ dune exec -- raven --shh --only p.loop_wrong ./only.rav
  [Error] File "./only.rav", line 12, columns 23-29:
  12 |     assert loop_wrong: i >= 1;
                              ^^^^^^
  Verification Error: Assertion 'loop_wrong': This assertion may be violated.
  [1]

Loop invariants can be named too; only the named one is checked, on entry and
when maintained.

  $ dune exec -- raven --shh --only count.bounded ./only.rav
  Verification successful.
  $ dune exec -- raven --shh --only count.wrong_step ./only.rav
  [Error] File "./only.rav", line 36, columns 26-32:
  36 |     invariant wrong_step: i <= 1
                                 ^^^^^^
  Verification Error: Assertion 'wrong_step': This loop invariant may not be maintained.
  [Error] File "./only.rav", line 36, columns 26-32:
  36 |     invariant wrong_step: i <= 1
                                 ^^^^^^
  Related Location: This assertion may not hold.
  [1]

So can an assertion with a proof block, and the assertions in its proof.

  $ dune exec -- raven --shh --only q.inner ./only.rav
  Verification successful.
  $ dune exec -- raven --shh --only q.wrong ./only.rav
  [Error] File "./only.rav", line 48, columns 16-21:
  48 |   assert wrong: x > 5 with {
                       ^^^^^
  Verification Error: Assertion 'wrong': This assertion may be violated.
  [1]

A name that names nothing is an error.

  $ dune exec -- raven --shh --only p.none ./only.rav
  [Error] Error: There is no member, module or named assertion p.none to verify
  [1]

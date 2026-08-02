  $ dune exec -- raven --shh ./is_recognizer_unsound_check.rav
  [Error] File "./is_recognizer_unsound_check.rav", line 13, columns 1-1:
  13 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./is_recognizer_unsound_check.rav", line 11, columns 10-19:
  11 |   ensures x is cons
                 ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

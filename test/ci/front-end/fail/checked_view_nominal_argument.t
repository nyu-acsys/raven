  $ dune exec -- raven --shh ./checked_view_nominal_argument.rav
  [Error] File "./checked_view_nominal_argument.rav", line 5, columns 27-33:
  5 | module Rejected = Consumer[Actual]
                                 ^^^^^^
  Type Error: Module Actual does not implement interface Required.
  [1]

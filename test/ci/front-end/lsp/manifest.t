`--manifest` reports what this binary is and what a client can expect of it: the release
version, the version of the machine-readable interface driven by `--lsp-mode` (its JSON
diagnostic schema and the flags a client relies on), and the oldest Z3 it works against.
An editor integration that fetches verifier builds it was not shipped with reads this to
decide whether it can drive a given binary.

That makes these compatibility promises rather than implementation details, so they are
recorded here. `lsp_protocol` in particular is versioned separately from the release and
should change only when an existing client would notice the difference -- re-promoting
this test is the moment to ask whether it has to.

  $ dune exec -- raven --manifest
  {"version":"1.2.0","lsp_protocol":1,"min_z3":"4.13.0"}

It is payload, not logging, so it survives `-q` and needs no `--shh`. A client asking
what it is talking to gets one line of JSON and nothing else.

  $ dune exec -- raven -q --manifest
  {"version":"1.2.0","lsp_protocol":1,"min_z3":"4.13.0"}

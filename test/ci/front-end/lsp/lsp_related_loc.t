In `--lsp-mode`, a related location must keep its own file, position and message, so
that an editor can turn it into a clickable jump to the declaration that was violated.
Both related locations below live in the file reached through `include`, and neither is
in the file being checked.

The absolute paths are rewritten relative to the sandbox, and one record per line, so
the expected output does not depend on where the test happens to run. The primary
diagnostic keeps pointing at the file being checked -- an LSP diagnostic is displayed in
the document it is reported against, so that one has nowhere else to go.

  $ dune exec -- raven --lsp-mode -q ./lsp_related_loc.rav | sed "s|$PWD/||g; s|},{|}\n{|g"
  [{"file":"included/lsp_iface.rav","start_line":7,"start_col":13,"end_line":7,"end_col":24,"kind":"RelatedLoc","message":["Lemma compCommute inherited from axiom MiniRA.compCommute"]}
  {"file":"./lsp_related_loc.rav","start_line":6,"start_col":10,"end_line":6,"end_col":10,"kind":"Verification","message":["A postcondition may not hold at this return point"]}
  {"file":"included/lsp_iface.rav","start_line":8,"start_col":59,"end_line":8,"end_col":83,"kind":"RelatedLoc","message":["This assertion may not hold"]}]

The message a related location used to be replaced with is gone entirely.

  $ dune exec -- raven --lsp-mode -q ./lsp_related_loc.rav | grep -c "originates in included file"
  0
  [1]

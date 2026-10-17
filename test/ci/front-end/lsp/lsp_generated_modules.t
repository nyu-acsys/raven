The module generated for `Seq[Int]` inherits `default` from `Library.Type`, just like
MyInt, but only MyInt is annotated. The `path` field is dropped, see lsp_library_loc.t.

  $ dune exec -- raven --shh -q --lsp-mode --lsp-annotations ./lsp_generated_modules.rav | sed 's|,"path":"[^"]*"||g'
  {"errors":[],"annotations":[{"file":"./lsp_generated_modules.rav","start_line":1,"start_col":7,"end_line":1,"end_col":12,"kind":"InheritedMembers","members":[{"origin":"Library.Type","text":"free val default: T","file":"lib/library/base_types.rav","start_line":6,"start_col":11,"end_line":6,"end_col":21,"library":true}]}],"members":[{"file":"./lsp_generated_modules.rav","start_line":5,"start_col":5,"end_line":5,"end_col":6,"name":"p","kind":"proc","status":"verified"}],"dependencies":[]}

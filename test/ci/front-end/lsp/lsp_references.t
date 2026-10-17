Each name a program uses is reported with what it refers to, where that is declared and
its declaration, for hovers and going to definitions in an editor.

  $ dune exec -- raven --shh -q --lsp-mode --lsp-annotations --typeonly ./lsp_references.rav | python3 lsp_references.py lsp_references.rav
  1:7 M -> M (module, lsp_references.rav:1): module M
  5:12 y -> y (variable, lsp_references.rav:4): y: Int
  5:21 x -> x (variable, lsp_references.rav:4): x: Int
  7:4 x -> x (variable, lsp_references.rav:4): x: Int
  7:8 x -> x (variable, lsp_references.rav:4): x: Int
  11:8 r -> r (variable, lsp_references.rav:10): r: Ref
  11:10 value -> M.value (field, lsp_references.rav:2): field value: Int
  11:17 v -> v (variable, lsp_references.rav:10): ghost v: Int
  15:13 cell -> M.cell (predicate, lsp_references.rav:10): pred cell(r: Ref; v: Int) { … }
  15:18 r -> r (variable, lsp_references.rav:14): r: Ref
  15:21 v -> v (variable, lsp_references.rav:14): ghost v: Int
  16:12 cell -> M.cell (predicate, lsp_references.rav:10): pred cell(r: Ref; v: Int) { … }
  16:17 r -> r (variable, lsp_references.rav:14): r: Ref
  16:20 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  16:27 v -> v (variable, lsp_references.rav:14): ghost v: Int
  18:11 cell -> M.cell (predicate, lsp_references.rav:10): pred cell(r: Ref; v: Int) { … }
  18:16 r -> r (variable, lsp_references.rav:14): r: Ref
  18:19 v -> v (variable, lsp_references.rav:14): ghost v: Int
  19:8 w -> w (variable, lsp_references.rav:19): w: Int
  19:13 r -> r (variable, lsp_references.rav:14): r: Ref
  19:15 value -> M.value (field, lsp_references.rav:2): field value: Int
  20:4 r -> r (variable, lsp_references.rav:14): r: Ref
  20:6 value -> M.value (field, lsp_references.rav:2): field value: Int
  20:15 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  20:22 w -> w (variable, lsp_references.rav:19): w: Int
  21:9 cell -> M.cell (predicate, lsp_references.rav:10): pred cell(r: Ref; v: Int) { … }
  21:14 r -> r (variable, lsp_references.rav:14): r: Ref
  21:17 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  21:24 v -> v (variable, lsp_references.rav:14): ghost v: Int
  25:15 Seq -> Library.Seq (module, base_types.rav:372): module Seq
  26:2 n -> n (variable, lsp_references.rav:25): n: Int
  26:9 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  27:6 t -> t (variable, lsp_references.rav:27): t: Set[Int]
  30:7 F -> F (module, lsp_references.rav:30): module F
  30:20 Type -> Library.Type (interface, base_types.rav:1): interface Type
  31:13 T -> F.T (interface, base_types.rav:1): module T: Type
  31:28 T -> F.T (interface, base_types.rav:1): module T: Type
  31:33 t -> t (variable, lsp_references.rav:31): t: F.T.T
  34:12 F -> F (module, lsp_references.rav:30): module F
  36:41 id -> FI.id (function, lsp_references.rav:31): func id(t: T) returns (r: T) { … }
  36:44 x -> x (variable, lsp_references.rav:36): x: Int

Each name a program uses is reported with what it refers to, where that is declared and
its declaration, for hovers and going to definitions in an editor.

  $ dune exec -- raven --shh -q --lsp-mode --lsp-annotations --typeonly ./lsp_references.rav | python3 lsp_references.py lsp_references.rav
  1:7 M -> M (module, lsp_references.rav:1): module M
  2:8 value -> M.value (field, lsp_references.rav:2): field value: Int
  4:7 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  4:14 x -> x (variable, lsp_references.rav:4): x: Int
  4:31 y -> y (variable, lsp_references.rav:4): y: Int
  5:12 y -> y (variable, lsp_references.rav:4): y: Int
  5:21 x -> x (variable, lsp_references.rav:4): x: Int
  7:4 x -> x (variable, lsp_references.rav:4): x: Int
  7:8 x -> x (variable, lsp_references.rav:4): x: Int
  10:7 cell -> M.cell (predicate, lsp_references.rav:10): pred cell(r: Ref; v: Int) { … }
  10:12 r -> r (variable, lsp_references.rav:10): r: Ref
  10:20 v -> v (variable, lsp_references.rav:10): ghost v: Int
  11:8 r -> r (variable, lsp_references.rav:10): r: Ref
  11:10 value -> M.value (field, lsp_references.rav:2): field value: Int
  11:17 v -> v (variable, lsp_references.rav:10): ghost v: Int
  14:7 inc -> M.inc (procedure, lsp_references.rav:14): proc inc(r: Ref, implicit ghost v: Int)
  14:11 r -> r (variable, lsp_references.rav:14): r: Ref
  14:34 v -> v (variable, lsp_references.rav:14): ghost v: Int
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
  25:5 client -> client (procedure, lsp_references.rav:25): proc client(s: Seq[Int]) returns (n: Int) { … }
  25:12 s -> s (variable, lsp_references.rav:25): s: Library.Seq[Int]
  25:15 Seq -> Library.Seq (module, base_types.rav:384): module Seq
  25:34 n -> n (variable, lsp_references.rav:25): n: Int
  26:2 n -> n (variable, lsp_references.rav:25): n: Int
  26:9 double -> M.double (function, lsp_references.rav:4): func double(x: Int) returns (y: Int)
  27:6 t -> t (variable, lsp_references.rav:27): t: Set[Int]
  30:7 F -> F (module, lsp_references.rav:30): module F
  30:20 Type -> Library.Type (interface, base_types.rav:1): interface Type
  31:7 id -> F.id (function, lsp_references.rav:31): func id(t: T) returns (r: T) { … }
  31:10 t -> t (variable, lsp_references.rav:31): t: F.T.T
  31:13 T -> F.T (interface, base_types.rav:1): module T: Type
  31:25 r -> r (variable, lsp_references.rav:31): r: F.T.T
  31:28 T -> F.T (interface, base_types.rav:1): module T: Type
  31:33 t -> t (variable, lsp_references.rav:31): t: F.T.T
  34:7 FI -> FI (module, lsp_references.rav:34): module FI = F[Int]
  34:12 F -> F (module, lsp_references.rav:30): module F
  36:5 use -> use (function, lsp_references.rav:36): func use(x: FI.T) returns (y: FI.T) { … }
  36:9 x -> x (variable, lsp_references.rav:36): x: Int
  36:12 FI -> FI (module, lsp_references.rav:34): module FI = F[Int]
  36:27 y -> y (variable, lsp_references.rav:36): y: Int
  36:30 FI -> FI (module, lsp_references.rav:34): module FI = F[Int]
  36:38 FI -> FI (module, lsp_references.rav:34): module FI = F[Int]
  36:41 id -> FI.id (function, lsp_references.rav:31): func id(t: T) returns (r: T) { … }
  36:44 x -> x (variable, lsp_references.rav:36): x: Int
  38:5 inferred -> inferred (function, lsp_references.rav:38): func inferred() returns (r: Int) { … }
  38:25 r -> r (variable, lsp_references.rav:38): r: Int
  38:35 F -> F (module, lsp_references.rav:30): module F
  38:37 id -> F.id (function, lsp_references.rav:31): func id(t: T) returns (r: T) { … }
  40:5 declared -> declared (procedure, lsp_references.rav:40): proc declared() { … }
  41:12 g -> g (variable, lsp_references.rav:41): ghost g: Int
  42:2 g -> g (variable, lsp_references.rav:41): ghost g: Int

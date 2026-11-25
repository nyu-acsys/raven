open Base
open Raven
open Ast
module Regions = Frontend.NamespaceRegions
module Embedding = Frontend.NamespaceRegionEmbedding

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi name = QualIdent.from_ident (id name)
let formal name = Type.mk_var_decl ~loc (id name) Type.int

let declaration ?alias ?(ancestry = NamespaceContract.Root) name parameters =
  NamespaceContract.
    {
      name = qi name;
      alias = Option.map alias ~f:qi;
      formals = List.map parameters ~f:formal;
      definition = Abstract;
      ancestry;
    }

let ancestor kind name parameters =
  NamespaceContract.Declared
    {
      ancestry_kind = kind;
      ancestry_target = qi name;
      ancestry_args =
        List.map parameters ~f:(fun name -> Expr.from_var_decl (formal name));
      ancestry_loc = loc;
    }

let get = function Ok value -> value | Error _ -> assert false

let rejected reason = function
  | Error (error : Regions.error) ->
      assert (String.is_substring error.message ~substring:reason)
  | Ok () -> assert false

let check ~expected ~actual mappings =
  let expected = get (Regions.create expected) in
  let actual = get (Regions.create actual) in
  Embedding.check ~expected ~actual
    ~visible:(List.map mappings ~f:(fun (name, _) -> qi name))
    ~mapping:(List.map mappings ~f:(fun (from, to_) -> (qi from, qi to_)))

let test_projection () =
  let expected_root = declaration "Root" [ "a"; "b" ] in
  let expected_child = declaration "Child" [ "left"; "right"; "key" ] in
  let expected =
    [
      expected_root;
      {
        expected_child with
        ancestry = ancestor Callable.Within "Root" [ "right"; "left" ];
      };
    ]
  in
  let root = declaration "ImplementationRoot" [ "r"; "s" ] in
  let child = declaration "ImplementationChild" [ "one"; "two"; "extra" ] in
  let actual parameters =
    [
      root;
      declaration
        ~ancestry:(ancestor Callable.Parent "ImplementationRoot" parameters)
        "Hidden" [ "first"; "slot"; "second" ];
      {
        child with
        ancestry = ancestor Callable.Parent "Hidden" [ "one"; "extra"; "two" ];
      };
    ]
  in
  let mappings = [ ("Root", "ImplementationRoot"); ("Child", "ImplementationChild") ] in
  let matching = actual [ "second"; "first" ] in
  get (check ~expected ~actual:matching mappings);
  rejected "changes the ancestry key projection"
    (check ~expected ~actual:(actual [ "first"; "second" ]) mappings);
  rejected "does not preserve ancestry" (check ~expected ~actual:[ root; child ] mappings);
  rejected "undeclared ancestor"
    (check ~expected:[ expected_root; expected_child ] ~actual:matching mappings)

let test_aliases () =
  let public = declaration "Public" [ "key" ] in
  let reexport = declaration ~alias:"Public" "Reexport" [ "x" ] in
  let supplied = declaration "Supplied" [ "y" ] in
  let supplied_alias = declaration ~alias:"Supplied" "Alias" [ "k" ] in
  let other = declaration "Other" [ "key" ] in
  let actual = [ supplied; supplied_alias; other ] in
  let mapping = [ ("Public", "Supplied"); ("Reexport", "Alias") ] in
  get (check ~expected:[ public; reexport ] ~actual mapping);
  rejected "identifies distinct invariants"
    (check ~expected:[ public; { reexport with alias = None } ] ~actual mapping);
  rejected "does not preserve the invariant alias"
    (check ~expected:[ public; reexport ] ~actual
       [ ("Public", "Supplied"); ("Reexport", "Other") ])

let test_identity_arity () =
  let expected = [ declaration "Public" [ "key" ] ] in
  let actual = [ declaration "Implementation" [ "owner"; "key" ] ] in
  rejected "different identity arity"
    (check ~expected ~actual [ ("Public", "Implementation") ])

let test_hidden_ancestor () =
  let expected = [ declaration "Public" [ "key" ] ] in
  let actual =
    [
      declaration "Hidden" [ "key" ];
      declaration
        ~ancestry:(ancestor Callable.Parent "Hidden" [ "key" ])
        "Implementation" [ "key" ];
    ]
  in
  rejected "undeclared ancestor"
    (check ~expected ~actual [ ("Public", "Implementation") ])

let () =
  test_projection ();
  test_aliases ();
  test_identity_arity ();
  test_hidden_ancestor ()

open Base
open Raven
open Ast
module Regions = Frontend.NamespaceRegions

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi name = QualIdent.from_ident (id name)
let formal ?(implicit = false) name = Type.mk_var_decl ~loc ~implicit (id name) Type.int
let variable name = Expr.from_var_decl (formal name)

let declaration ?(ancestry = NamespaceContract.Root) name parameters =
  NamespaceContract.
    {
      name = qi name;
      formals = List.map parameters ~f:formal;
      definition = Abstract;
      ancestry;
      alias = None;
    }

let ancestor ?(kind = Callable.Parent) name arguments =
  NamespaceContract.Declared
    {
      ancestry_kind = kind;
      ancestry_target = qi name;
      ancestry_args = arguments;
      ancestry_loc = loc;
    }

let parent ?(within = false) name parameters =
  ancestor
    ~kind:(if within then Callable.Within else Parent)
    name
    (List.map parameters ~f:variable)

let get = function Ok value -> value | Error _ -> assert false
let rejected = function Error _ -> () | Ok _ -> assert false

let declarations () =
  [
    declaration "Root" [ "owner" ];
    declaration "Other" [ "owner" ];
    declaration ~ancestry:(parent "Root" [ "owner" ]) "Child" [ "owner"; "key" ];
    declaration ~ancestry:(parent "Child" [ "o"; "k" ]) "Grandchild" [ "k"; "slot"; "o" ];
    declaration
      ~ancestry:(parent ~within:true "Root" [ "owner" ])
      "AbstractChild" [ "owner" ];
    declaration ~ancestry:(parent "Root" [ "owner" ]) "Swapped" [ "key"; "owner" ];
  ]

let region hierarchy name args =
  get (Regions.region hierarchy (qi name) (List.map args ~f:Expr.mk_int))

let test_transitive_projection hierarchy =
  assert (Option.is_some (Regions.declaration hierarchy (qi "Root")));
  assert (Option.is_some (Regions.declaration hierarchy (qi "Grandchild")));
  assert (Option.is_some (Regions.declaration hierarchy (qi "Other")));
  assert (
    Option.equal (List.equal Int.equal)
      (Regions.projection hierarchy ~descendant:(qi "Grandchild") ~ancestor:(qi "Root"))
      (Some [ 2 ]));
  assert (
    Option.equal (List.equal Int.equal)
      (Regions.projection hierarchy ~descendant:(qi "Grandchild") ~ancestor:(qi "Child"))
      (Some [ 2; 0 ]));
  assert (
    Option.is_none
      (Regions.projection hierarchy ~descendant:(qi "Root") ~ancestor:(qi "Child")));
  assert (
    Option.is_none
      (Regions.projection hierarchy ~descendant:(qi "Other") ~ancestor:(qi "Child")));
  match Regions.declaration hierarchy (qi "AbstractChild") with
  | Some { ancestry = Declared { ancestry_kind = Within; _ }; _ } -> ()
  | _ -> assert false

let test_coverage hierarchy =
  let root = region hierarchy "Root" [ 7 ] in
  let child = region hierarchy "Child" [ 7; 3 ] in
  let grandchild = region hierarchy "Grandchild" [ 3; 9; 7 ] in
  let wrong_owner = region hierarchy "Grandchild" [ 3; 9; 8 ] in
  let other = region hierarchy "Other" [ 7 ] in
  assert (Regions.covers hierarchy ~by:root root);
  assert (Regions.covers hierarchy ~by:root child);
  assert (Regions.covers hierarchy ~by:root grandchild);
  assert (Regions.covers hierarchy ~by:child grandchild);
  assert (not (Regions.covers hierarchy ~by:child root));
  assert (not (Regions.covers hierarchy ~by:root wrong_owner));
  assert (not (Regions.covers hierarchy ~by:other child))

let test_prefixes hierarchy =
  let all = region hierarchy "Root" [] in
  let root = region hierarchy "Root" [ 7 ] in
  let children = region hierarchy "Child" [ 7 ] in
  let swapped = region hierarchy "Swapped" [ 3 ] in
  let specific = region hierarchy "Swapped" [ 3; 7 ] in
  assert (Regions.covers hierarchy ~by:all swapped);
  assert (Regions.covers hierarchy ~by:root children);
  assert (not (Regions.covers hierarchy ~by:root swapped));
  assert (Regions.covers hierarchy ~by:root specific);
  assert (not (Regions.covers hierarchy ~by:swapped root));
  assert (Regions.covers hierarchy ~by:swapped specific);
  rejected (Regions.region hierarchy (qi "Root") [ Expr.mk_int 7; Expr.mk_int 3 ]);
  rejected (Regions.region hierarchy (qi "Unknown") [])

let test_symbolic_arguments hierarchy =
  let root = get (Regions.region hierarchy (qi "Root") [ variable "x" ]) in
  let child_x =
    get (Regions.region hierarchy (qi "Child") [ variable "x"; Expr.mk_int 1 ])
  in
  let child_y =
    get (Regions.region hierarchy (qi "Child") [ variable "y"; Expr.mk_int 1 ])
  in
  assert (Regions.covers hierarchy ~by:root child_x);
  (* Equality of x and y is a later proof obligation. *)
  assert (not (Regions.covers hierarchy ~by:root child_y))

let test_invalid_hierarchies () =
  let root = declaration "Root" [ "x" ] in
  rejected (Regions.create [ { root with ancestry = Unresolved } ]);
  rejected (Regions.create [ root; root ]);
  rejected
    (Regions.create [ declaration ~ancestry:(parent "Missing" [ "x" ]) "I" [ "x" ] ]);
  rejected (Regions.create [ root; declaration ~ancestry:(parent "Root" []) "I" [ "x" ] ]);
  rejected
    (Regions.create
       [ root; declaration ~ancestry:(parent "Root" [ "unbound" ]) "I" [ "x" ] ]);
  let transformed =
    ancestor "Root" [ Expr.mk_app ~typ:Type.int (Var (qi "f")) [ variable "x" ] ]
  in
  rejected (Regions.create [ root; declaration ~ancestry:transformed "I" [ "x" ] ]);
  let implicit = declaration ~ancestry:(parent "Root" [ "x" ]) "I" [ "x" ] in
  rejected
    (Regions.create [ root; { implicit with formals = [ formal ~implicit:true "x" ] } ]);
  rejected
    (Regions.create [ declaration ~ancestry:(parent "Self" [ "x" ]) "Self" [ "x" ] ]);
  rejected
    (Regions.create
       [
         declaration ~ancestry:(parent "B" [ "x" ]) "A" [ "x" ];
         declaration ~ancestry:(parent "A" [ "y" ]) "B" [ "y" ];
       ])

let test_implicit_identity () =
  let declaration = declaration "I" [ "owner"; "key" ] in
  let declaration =
    { declaration with formals = [ formal "owner"; formal ~implicit:true "key" ] }
  in
  let hierarchy = get (Regions.create [ declaration ]) in
  let family = region hierarchy "I" [ 7 ] in
  let first = region hierarchy "I" [ 7; 1 ] in
  let second = region hierarchy "I" [ 7; 2 ] in
  assert (Regions.covers hierarchy ~by:family first);
  assert (not (Regions.covers hierarchy ~by:first family));
  assert (not (Regions.covers hierarchy ~by:first second))

let test_aliases_and_regions () =
  let root = declaration "Root" [ "key" ] in
  let alias = { (declaration "Alias" [ "key" ]) with alias = Some (qi "Root") } in
  let child = declaration ~ancestry:(parent "Alias" [ "key" ]) "Child" [ "key" ] in
  let hierarchy = get (Regions.create [ root; alias; child ]) in
  assert (Option.is_some (Regions.declaration hierarchy (qi "Alias")));
  assert (Regions.is_declared_regional hierarchy (qi "Root"));
  assert (
    Option.equal QualIdent.equal
      (Regions.canonical_name hierarchy (qi "Alias"))
      (Some (qi "Root")));
  assert (
    Regions.covers hierarchy
      ~by:(region hierarchy "Alias" [ 1 ])
      (region hierarchy "Child" [ 1 ]));
  let abstract = get (Regions.create [ root; alias ]) in
  assert (Option.is_some (Regions.declaration abstract (qi "Alias")));
  assert (not (Regions.is_declared_regional abstract (qi "Alias")));
  assert (
    Regions.covers abstract
      ~by:(region abstract "Alias" [ 1 ])
      (region abstract "Root" [ 1 ]));
  rejected (Regions.create [ alias ]);
  rejected (Regions.create [ root; { alias with alias = Some (qi "Alias") } ]);
  rejected (Regions.create [ root; { alias with formals = [] } ]);
  rejected (Regions.create [ root; { alias with ancestry = parent "Root" [ "key" ] } ])

let () =
  let hierarchy = get (Regions.create (declarations ())) in
  test_transitive_projection hierarchy;
  test_coverage hierarchy;
  test_prefixes hierarchy;
  test_symbolic_arguments hierarchy;
  test_invalid_hierarchies ();
  test_implicit_identity ();
  test_aliases_and_regions ()

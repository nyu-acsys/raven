open Base
open Raven
open Ast

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi names = QualIdent.from_list (List.map names ~f:id)
let own name prefix = Callable.invariant_mask_entry (qi name) prefix
let dependencies name prefix = (Callable.MaskHead.Dependencies (qi name), prefix)
let mask entries = Callable.mask_canon entries
let same_mask = Callable.mask_equal

let test_prefixes () =
  let own_region = [ own [ "P" ] [] ] in
  let dependency_region = [ dependencies [ "P" ] [] ] in
  assert (List.length (Callable.mask_union own_region dependency_region) = 2);
  assert (List.is_empty (Callable.mask_inter own_region dependency_region));
  List.iter [ own; dependencies ] ~f:(fun entry ->
      let broad = [ entry [ "P" ] [ Expr.mk_int 1 ] ] in
      let narrow = [ entry [ "P" ] [ Expr.mk_int 1; Expr.mk_int 2 ] ] in
      let other = [ entry [ "P" ] [ Expr.mk_int 2 ] ] in
      assert (same_mask (Callable.mask_union broad narrow) broad);
      assert (same_mask (Callable.mask_inter broad narrow) narrow);
      assert (List.is_empty (Callable.mask_inter broad other)))

let requirement left right : NamespaceContract.separation_requirement =
  { left; right; loc }

let test_collapsing_substitution () =
  let left = mask [ own [ "P" ] []; dependencies [ "P" ] [] ] in
  let right = mask [ own [ "Q" ] []; dependencies [ "Q" ] [] ] in
  let summary =
    NamespaceContract.Module
      {
        namespaces = [];
        separation = [ requirement left right ];
        callables =
          [
            ( id "call",
              {
                formals = [];
                returns = [];
                requires = Callable.mask_union left right;
                grants = left;
                separation = [ requirement left right ];
              } );
          ];
        modules = [];
      }
  in
  let mapped =
    NamespaceContract.map ~name:(fun _ -> qi [ "Actual" ]) ~expr:Fn.id ~typ:Fn.id summary
  in
  match mapped with
  | Module { separation = [ separation ]; callables = [ (_, callable) ]; _ } ->
      assert (same_mask separation.left separation.right);
      assert (List.length callable.requires = 2);
      assert (List.length callable.separation = 1);
      assert (same_mask callable.grants separation.left)
  | _ -> assert false

let test_unknown_namespace () =
  let declaration : NamespaceContract.namespace_decl =
    { name = qi [ "P" ]; formals = []; definition = Abstract }
  in
  let mapped definition =
    NamespaceContract.map_namespace_decl ~name:Fn.id ~expr:Fn.id ~typ:Fn.id
      { declaration with definition }
  in
  begin match ((mapped Abstract).definition, (mapped (Defined [])).definition) with
  | Abstract, Defined [] -> ()
  | _ -> assert false
  end;
  assert (Option.is_none Module.empty_decl.mod_decl_mask_contract);
  let frozen =
    { Module.empty_decl with mod_decl_mask_contract = Some NamespaceContract.empty }
  in
  match (Module.with_formals frozen []).mod_decl_mask_contract with
  | Some (Module { namespaces = []; separation = []; callables = []; modules = [] }) -> ()
  | _ -> assert false

let source name = qi [ "Source"; name ]
let target name = qi [ "Target"; name ]

let rename =
  QualIdent.requalify [ (qi [ "Source" ], QualIdent.to_list (qi [ "Target" ])) ]

let named_type name = Type.mk_app (Var name) []
let formal = Type.mk_var_decl ~loc (id "x") (named_type (source "T"))
let returned = Type.mk_var_decl ~loc (id "result") (named_type (source "T"))

let argument =
  Expr.mk_app ~typ:formal.var_type (Var (source "value")) [ Expr.from_var_decl formal ]

let higher_order_summary () =
  let open NamespaceContract in
  let region = [ dependencies [ "Source"; "P" ] [ argument ] ] in
  let declaration =
    { name = source "P"; formals = [ formal ]; definition = Defined region }
  in
  let result =
    Module
      {
        namespaces = [ declaration ];
        separation = [ requirement region [ own [ "Source"; "I" ] [] ] ];
        callables =
          [
            ( id "call",
              {
                formals = [ formal ];
                returns = [ returned ];
                requires = region;
                grants = region;
                separation = [];
              } );
          ];
        modules = [];
      }
  in
  Functor
    {
      parameters = [ (id "G", Functor { parameters = []; separation = []; result }) ];
      separation = [];
      result;
    }

let check_higher_order = function
  | NamespaceContract.Functor
      {
        parameters = [ (binder, Functor { parameters = []; result = Module nested; _ }) ];
        result = Module result;
        _;
      } ->
      assert (Ident.equal binder (id "G"));
      List.iter [ nested; result ] ~f:(fun summary ->
          match (summary.namespaces, summary.callables) with
          | [ declaration ], [ (call_name, callable) ] ->
              assert (Ident.equal call_name (id "call"));
              assert (QualIdent.equal declaration.name (target "P"));
              let transformed = List.hd_exn declaration.formals in
              assert (Ident.equal transformed.var_name formal.var_name);
              assert (Type.equal transformed.var_type (named_type (target "T")));
              List.iter
                [ (callable.formals, formal); (callable.returns, returned) ]
                ~f:(fun (binders, original) ->
                  let binder = List.hd_exn binders in
                  assert (Ident.equal binder.var_name original.Type.var_name);
                  assert (Type.equal binder.var_type (named_type (target "T"))));
              let expected =
                Expr.mk_app ~typ:transformed.var_type
                  (Var (target "value"))
                  [ Expr.from_var_decl transformed ]
              in
              let expected_mask = [ dependencies [ "Target"; "P" ] [ expected ] ] in
              assert (same_mask callable.requires expected_mask);
              assert (same_mask callable.grants expected_mask);
              begin match declaration.definition with
              | Defined body -> assert (same_mask body expected_mask)
              | Abstract -> assert false
              end;
              assert (List.length summary.separation = 1)
          | _ -> assert false)
  | _ -> assert false

let test_requalification () =
  let summary = higher_order_summary () in
  let _, rewritten =
    Rewriter.eval
      (Rewriter.NamespaceContract.rewrite_qual_idents ~f:rename summary)
      (SymbolTbl.create ())
  in
  check_higher_order rewritten;
  let definition =
    Module.
      {
        mod_decl =
          {
            empty_decl with
            mod_decl_name = id "Owner";
            mod_decl_mask_contract = Some summary;
          };
        mod_def = [];
      }
  in
  let rewrite =
    let open Rewriter.Syntax in
    let* () = Rewriter.declare_symbol (Module.ModDef definition) in
    Rewriter.Module.rewrite_qual_idents ~f:rename definition
  in
  let _, rewritten = Rewriter.eval rewrite (SymbolTbl.create ()) in
  match rewritten.mod_decl.mod_decl_mask_contract with
  | Some summary -> check_higher_order summary
  | None -> assert false

let () =
  test_prefixes ();
  test_collapsing_substitution ();
  test_unknown_namespace ();
  test_requalification ()

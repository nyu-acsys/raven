open Base
open Ast
open Util

let validate ~regions ~namespaces program =
  let open Rewriter.Syntax in
  List.iter namespaces ~f:(fun (declaration : NamespaceContract.namespace_decl) ->
      match declaration.ancestry with
      | Declared ({ ancestry_kind = Parent; _ } as parent) ->
          let child = NamespaceRegions.canonical_name regions declaration.name in
          let ancestor = NamespaceRegions.canonical_name regions parent.ancestry_target in
          begin match (child, ancestor) with
          | Some child, Some ancestor
            when QualIdent.is_qualified child
                 && QualIdent.is_qualified ancestor
                 && QualIdent.equal (QualIdent.pop child) (QualIdent.pop ancestor) ->
              ()
          | _ ->
              Error.type_error parent.ancestry_loc
                "A concrete parent must belong to the same invariant family module"
          end
      | Root | Declared { ancestry_kind = Within; _ } -> ()
      | Unresolved ->
          Error.type_error
            (QualIdent.to_loc declaration.name)
            "Unresolved invariant ancestry");
  let check symbol =
    begin match symbol with
    | Module.CallDef call ->
        Option.iter call.call_decl.call_decl_bound ~f:(fun clause ->
            List.iter (Callable.bound_mask clause) ~f:(fun (head, args) ->
                let name = Callable.mask_head_name head in
                match NamespaceRegions.declaration regions name with
                | Some declaration
                  when Callable.is_invariant_head head
                       && List.length args > List.length declaration.formals ->
                    Error.type_error clause.bound_loc
                      "An opens entry for a region may specify only identity parameters"
                | _ -> ()))
    | _ -> ()
    end;
    Rewriter.return symbol
  in
  let+ _ = Rewriter.Module.rec_rewrite_symbols ~f:check program in
  ()

open Base
open Ast
open Util

type t = { name : QualIdent.t; substitution : QualIdent.subst }

let parent_methods symbol =
  Rewriter.Symbol.extract symbol ~f:(fun _ _ -> function
    | Module.ModDef parent ->
        List.filter_map parent.mod_def ~f:(function
          | Module.SymbolDef (CallDef ({ call_decl; _ } as call)) ->
              begin match call_decl.call_decl_kind with
              | Callable.Proc | Lemma -> Some call
              | Func | Pred | Invariant -> None
              end
          | Module.SymbolDef _ | Module.Import _ -> None)
    | symbol ->
        Error.internal_error (Symbol.to_loc symbol)
          "A nominal parent must resolve to a module definition")

let find ~owner (decl : Callable.call_decl) : (t option, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* owner_symbol = Rewriter.find owner in
  let parents, instances =
    Rewriter.Symbol.extract owner_symbol ~f:(fun _ _ -> function
      | Module.ModDef module_ ->
          (module_.mod_decl.mod_decl_returns, module_.mod_decl.mod_decl_instance_subst)
      | _ -> ([], []))
  in
  let* candidates =
    Rewriter.List.map parents ~f:(fun parent ->
        let* parent_symbol = Interfaces.realize_parent ~owner parent in
        let parent_name = Rewriter.Symbol.orig_qid parent_symbol in
        let matches =
          parent_methods parent_symbol
          |> List.filter ~f:(fun call ->
              let source = call.Callable.call_decl in
              Poly.(source.call_decl_kind = decl.call_decl_kind)
              && String.equal
                   (Ident.name source.call_decl_name)
                   (Ident.name decl.call_decl_name))
        in
        Rewriter.return
          (List.map matches ~f:(fun call ->
               let name =
                 QualIdent.append parent_name call.Callable.call_decl.call_decl_name
               in
               { name; substitution = Rewriter.Symbol.subst parent_symbol @ instances })))
  in
  match List.concat candidates with
  | [] -> Rewriter.return None
  | [ origin ] -> Rewriter.return (Some origin)
  | _ ->
      Error.type_error decl.call_decl_loc
        "The callable matches declarations in multiple parent modules"
